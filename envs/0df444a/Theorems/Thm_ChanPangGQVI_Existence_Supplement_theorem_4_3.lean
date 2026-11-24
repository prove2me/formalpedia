-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_Supplement_theorem_4_3
-- name    : ChanPangGQVI.Existence.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:56:43.323802+00:00
-- url     : https://prove2.me/theorems/f74d3c21-c7d0-445a-8e13-a2733e83f1a1
-- title:
--   Theorem 4.3 — existence for GQVI(K, f) with f pseudo-monotone with respect to K and y⁰ interior to the dual of ⋃ K(x)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean inner product and norm, and write $B_\rho=\{x:\|x\|\le\rho\}$. For a set $S$, $S^*=\{y : y^T z\ge 0\ \text{for all}\ z\in S\}$ is its dual and $(S^*)^0$ the interior of $S^*$. Let $f$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself and suppose:
--
--   1. there are vectors
--   $$
--   x^0\in\bigcap_{x\in\mathbb R^n}K(x),\qquad y^0\in f(x^0)\cap\Big[\Big(\bigcup_{x\in\mathbb R^n}K(x)\Big)^*\Big]^0 ;
--   $$
--   2. $f$ is pseudo-monotone with respect to $K$: for $x\in K(x)$, $x'\in K(x')$, $y\in f(x)$, $y'\in f(x')$, $(x'-x)^T y\ge0$ implies $(x'-x)^T y'\ge0$;
--   3. (condition (i) of Corollary 4.1) $f$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $\mathbb R^n$, and $K$ is convex valued;
--   4. (condition (ii) of Corollary 4.1) there is $\rho_0>0$ such that for every $\rho\ge\rho_0$ the mapping $x\mapsto K(x)\cap B_\rho$ is continuous (upper and lower semicontinuous) on $\mathbb R^n$ with closed values.
--
--   Then $\mathrm{GQVI}(K,f)$ has a solution:
--
--   $$
--   \exists x,y\in\mathbb R^n:\quad x\in K(x),\quad y\in f(x),\quad
--   (x'-x)^T y\ge 0\quad\text{for every }x'\in K(x).
--   $$
--
--   The coercivity condition (4) of Corollary 4.1 is not assumed: pseudo-monotonicity and the interior point $y^0$ replace it. The theorem extends existence results for pseudo-monotone variational inequalities to the set-valued, quasi-variational setting.
--
--   **Formalization Note** The dual set is `dualConeSet` of the base mission and the interior is Mathlib's `interior`. Conditions (i)–(ii) of Corollary 4.1 are written exactly as in the published `ChanPangGQVI.Existence.corollary_4_1`, with $f$ in place of $\mu$. Closed values of $K(x)\cap B_\rho$ are Berge's convention for upper semicontinuous mappings (compact values), as in that corollary.
--
--   Differences from the source:
--   - reading: K(x) ∩ B_ρ continuous (Berge) → in addition K(x) ∩ B_ρ closed for every x and ρ ≥ ρ₀; reason: Berge's upper semicontinuous mappings have compact values; without it the theorem fails (n = 1, K ≡ (0, 1), f ≡ {1}, x⁰ = 1/2, y⁰ = 1 meets every printed hypothesis and GQVI(K, f) has no solution).
--   - encoding: "conditions (i) and (ii) of Corollary 4.1" → the hypotheses of the published corollary_4_1 with f for μ (UpperHemicontinuous f, Upper/LowerHemicontinuous of x ↦ K(x) ∩ closedBall 0 ρ); reason: transcription of the cited conditions; Berge's semicontinuity on ℝⁿ; same instances.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 219, Theorem 4.3

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
import Definitions.Def_ChanPangGQVI_Existence_Supplement_PseudoMonotone

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence.Supplement

open ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 219, Theorem 4.3. Let `f`, `K` be point-to-set mappings of `ℝⁿ`.
Suppose there exist `x⁰ ∈ ⋂_{all x} K(x)` and `y⁰ ∈ f(x⁰) ∩ [(⋃_{x ∈ ℝⁿ} K(x))*]⁰`, that `f` is
pseudo-monotone with respect to `K`, and that conditions (i) and (ii) of Corollary 4.1 hold:
(i) `f` is a nonempty contractible compact valued upper semicontinuous mapping on `ℝⁿ` and `K` is
convex valued; (ii) there is `ρ₀ > 0` such that `K(x) ∩ B_ρ` is a continuous mapping for all
`ρ ≥ ρ₀`. Then `GQVI(K, f)` has a solution.

`[S*]⁰` is the interior of the dual set `S* = {y | yᵀ z ≥ 0 ∀ z ∈ S}` (`dualConeSet`). Conditions
(i)–(ii) are written as in the published `corollary_4_1`, with `f` for `μ`; "continuous mapping"
is upper and lower hemicontinuity on `ℝⁿ`. Implicit hypothesis made explicit: `K(x) ∩ B_ρ` is
closed for every `x` and `ρ ≥ ρ₀` (`hKB_closed`, Berge's compact values). Condition (4) of
Corollary 4.1 is not assumed. -/
theorem theorem_4_3 {n : ℕ} (f K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 y0 : EuclideanSpace ℝ (Fin n)) (hx0 : ∀ x, x0 ∈ K x)
    (hy0f : y0 ∈ f x0) (hy0 : y0 ∈ interior (dualConeSet (⋃ x, K x)))
    (hpm : IsPseudoMonotoneWRT f K)
    (hf_ne : ∀ x, (f x).Nonempty) (hf_contr : ∀ x, IsContractibleSet (f x))
    (hf_cpt : ∀ x, IsCompact (f x)) (hf_usc : UpperHemicontinuous f)
    (hK_conv : ∀ x, Convex ℝ (K x))
    (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (hKB_usc : ∀ ρ ≥ ρ0,
      UpperHemicontinuous (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ))
    (hKB_lsc : ∀ ρ ≥ ρ0,
      LowerHemicontinuous (fun x => K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ))
    (hKB_closed : ∀ ρ ≥ ρ0, ∀ x,
      IsClosed (K x ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ)) :
    ∃ x y : EuclideanSpace ℝ (Fin n), IsGQVISolution K f x y := by sorry

end ChanPangGQVI.Existence.Supplement
