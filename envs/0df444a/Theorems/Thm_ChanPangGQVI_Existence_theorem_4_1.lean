-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_theorem_4_1
-- name    : ChanPangGQVI.Existence.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:38:55.303303+00:00
-- url     : https://prove2.me/theorems/b9d8bf5b-eafd-447c-a941-03cc356d8973
-- title:
--   Theorem 4.1 — GQVI(K, μ + q) has a solution in B_r whenever ‖q‖ ≤ C_{μ,K}(r, x⁰)
-- statement:
--   Let $\mu$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself; $B_r$ is the closed ball of radius $r$ about the origin, $C_r$ its boundary sphere and $B_r^0$ the open ball. Suppose that
--
--   1. there are $r>0$ and $x^0\in\big(\bigcap_{x\in C_r}K(x)\big)\cap B_r^0$ with $C_{\mu,K}(r,x^0)\ge 0$;
--   2. $\mu$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $B_r$;
--   3. $K(x)$ is convex for $x\in B_r$, and $x\mapsto K(x)\cap B_r$ is a nonempty, continuous mapping on $B_r$ with closed values.
--
--   Then for each vector $q\in\mathbb R^n$ with
--
--   $$
--   \|q\|\ \le\ C_{\mu,K}(r,x^0),
--   $$
--
--   $\mathrm{GQVI}(K,\mu+q)$ has a solution $(x,y)$ with $x\in B_r$.
--
--   The coercivity function $C_{\mu,K}(r,x^0)$ is defined on p. 217 of the paper (see the definition item); the infimum over an empty set is $+\infty$. The theorem converts a lower bound on this function into existence for all perturbations $q$ of bounded size.
--
--   **Formalization Note** Both bounds on $C_{\mu,K}$ are expressed through `CoercivityGE` (with $c=0$ and $c=\|q\|$). The closedness of $K(x)\cap B_r$ is Berge's compact-values convention, made explicit.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 217, Theorem 4.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
import Definitions.Def_ChanPangGQVI_Existence_Coercivity

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 217, Theorem 4.1. Let `μ`, `K` be point-to-set mappings of `ℝⁿ`.
Suppose (i) `r > 0` and `x⁰ ∈ (⋂_{x ∈ C_r} K(x)) ∩ B_r°` satisfy `C_{μ,K}(r, x⁰) ≥ 0`;
(ii) `μ` is a nonempty contractible compact valued upper semicontinuous mapping on `B_r`;
(iii) `K(x)` is convex valued on `B_r` and `K(x) ∩ B_r` is a nonempty continuous mapping on `B_r`.
Then for each `q` with `‖q‖ ≤ C_{μ,K}(r, x⁰)`, `GQVI(K, μ + q)` has a solution in `B_r`.

`B_r` is the closed ball of radius `r` about `0`, `C_r` its boundary sphere, `B_r°` the open ball.
`C_{μ,K}(r, x⁰) ≥ c` is `CoercivityGE μ K r x0 c` (infimum over `∅` is `∞`). Implicit hypothesis
made explicit: `K(x) ∩ B_r` is closed for `x ∈ B_r` (`hKB_closed`, Berge's compact values). -/
theorem theorem_4_1 {n : ℕ} (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (hr : 0 < r) (x0 : EuclideanSpace ℝ (Fin n))
    (hx0K : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r, x0 ∈ K x)
    (hx0B : x0 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
    (hC : CoercivityGE μ K r x0 0)
    (hμ_ne : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, (μ x).Nonempty)
    (hμ_contr : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      IsContractibleSet (μ x))
    (hμ_cpt : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, IsCompact (μ x))
    (hμ_usc : UpperHemicontinuousOn μ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
    (hK_conv : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, Convex ℝ (K x))
    (hKB_ne : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      (K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).Nonempty)
    (hKB_usc : UpperHemicontinuousOn
      (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
    (hKB_lsc : LowerHemicontinuousOn
      (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
    (hKB_closed : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      IsClosed (K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)) :
    ∀ q : EuclideanSpace ℝ (Fin n), CoercivityGE μ K r x0 ‖q‖ →
      ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
        ∃ y : EuclideanSpace ℝ (Fin n), IsGQVISolution K (shiftMap μ q) x y := by sorry

end ChanPangGQVI.Existence
