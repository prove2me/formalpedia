-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_corollary_4_1
-- name    : ChanPangGQVI.Existence.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:39:35.135466+00:00
-- url     : https://prove2.me/theorems/e129911f-6b50-4130-8474-3c01182213ef
-- title:
--   Corollary 4.1 — under coercivity (4), GQVI(K, μ + q) is solvable for every q and its solutions are bounded
-- statement:
--   Let $\mu$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself, and suppose there is a vector $x^0$ with $x^0\in K(x)$ for all $x\in\mathbb R^n$ such that
--
--   $$
--   \lim_{\|x\|\to\infty,\ x\in K(x)}\ \inf_{y\in\mu(x)}\frac{(x-x^0)^T y}{\|x\|}=\infty. \tag{4}
--   $$
--
--   Suppose also that
--
--   1. $\mu$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $\mathbb R^n$, and $K$ is convex valued;
--   2. there is $\rho_0>0$ such that for every $\rho\ge\rho_0$ the mapping $x\mapsto K(x)\cap B_\rho$ is continuous on $\mathbb R^n$ with closed values.
--
--   Then for each vector $q$, $\mathrm{GQVI}(K,\mu+q)$ has a solution. Moreover, for each $q$ there is $r>0$ such that $\|x^*\|<r$ for every solution $(x^*,y^*)$ of $\mathrm{GQVI}(K,\mu+q)$.
--
--   **Formalization Note** Condition (4) is `IsCoerciveAt μ K x0`. The bound $r$ is chosen after $q$ and may depend on it: no bound uniform in $q$ holds in general. "Continuous" means upper and lower hemicontinuous on all of $\mathbb R^n$; the closedness of $K(x)\cap B_\rho$ is Berge's compact-values convention, made explicit.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), pp. 217–218, Corollary 4.1 (condition (4) on p. 217)

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
import Definitions.Def_ChanPangGQVI_Existence_Coercivity

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, pp. 217–218, Corollary 4.1. Let `μ`, `K` be point-to-set mappings of `ℝⁿ`
and `x⁰ ∈ ⋂_{x ∈ ℝⁿ} K(x)` such that `lim_{‖x‖→∞, x ∈ K(x)} inf_{y ∈ μ(x)} (x - x⁰)ᵀ y / ‖x‖ = ∞`
(condition (4), `IsCoerciveAt μ K x0`). Suppose also (i) `μ` is a nonempty contractible compact
valued upper semicontinuous mapping on `ℝⁿ` and `K` is convex valued; (ii) there is `ρ₀ > 0` such
that `K(x) ∩ B_ρ` is a continuous mapping for all `ρ ≥ ρ₀`. Then for each `q`, `GQVI(K, μ + q)` has
a solution; moreover there is `r > 0` with `‖x*‖ < r` for each solution `(x*, y*)`.

"Continuous mapping" in (ii) is upper and lower hemicontinuity on all of `ℝⁿ`. Implicit hypothesis
made explicit: `K(x) ∩ B_ρ` is closed for every `x` and `ρ ≥ ρ₀` (`hKB_closed`, Berge's compact
values). The bound `r` is chosen after `q`: it may depend on `q`. -/
theorem corollary_4_1 {n : ℕ} (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : ∀ x, x0 ∈ K x)
    (h4 : IsCoerciveAt μ K x0)
    (hμ_ne : ∀ x, (μ x).Nonempty) (hμ_contr : ∀ x, IsContractibleSet (μ x))
    (hμ_cpt : ∀ x, IsCompact (μ x)) (hμ_usc : UpperHemicontinuous μ)
    (hK_conv : ∀ x, Convex ℝ (K x))
    (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (hKB_usc : ∀ ρ ≥ ρ0,
      UpperHemicontinuous (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ))
    (hKB_lsc : ∀ ρ ≥ ρ0,
      LowerHemicontinuous (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ))
    (hKB_closed : ∀ ρ ≥ ρ0, ∀ x,
      IsClosed (K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ)) :
    ∀ q : EuclideanSpace ℝ (Fin n),
      (∃ x y : EuclideanSpace ℝ (Fin n), IsGQVISolution K (shiftMap μ q) x y) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ x y : EuclideanSpace ℝ (Fin n), IsGQVISolution K (shiftMap μ q) x y → ‖x‖ < r := by sorry

end ChanPangGQVI.Existence
