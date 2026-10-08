-- Prove2me | Theorems.Thm_FastBestSubset_PSI_same_objective
-- name    : FastBestSubset.PSI.same_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:17.717007+00:00
-- url     : https://prove2.me/theorems/06dc1e9a-1510-40a7-804d-84dae584b812
-- title:
--   Proof of Theorem 4 (§A.8) — a CW minimum minimizes f on its support; CW minima with the same support have the same objective
-- statement:
--   Consider Problem (2) with unit-norm columns of $X$, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$. Then:
--
--   1. every CW minimum $b$ with support $S$ minimizes $f$ over the vectors supported in $S$:
--   $$f(b)\le f(\gamma)\qquad\text{for every }\gamma\in\mathbb R^p\text{ with }\gamma_i=0\text{ for all }i\notin S;$$
--   2. any two CW minima $b,b'$ with $\operatorname{Supp}(b)=\operatorname{Supp}(b')$ satisfy $F(b)=F(b')$.
--
--   This is the unnumbered step of the proof of Theorem 4: a CW minimum on a support $S$ is stationary for $\min_{\beta_S}f(\beta_S)$, and by convexity all such stationary points have the same value. Because the outputs of Algorithm 1 inside Algorithm 2 have strictly decreasing objective, it follows that their supports are pairwise distinct.
--
--   **Formalization Note** "Supported in $S$" is $\gamma_i=0$ for every $i\notin\operatorname{Supp}(b)$. Part 2 follows from Part 1 and $F=f+\lambda_0|S|$ on vectors with support $S$; both parts are stated so that the intermediate claim is a target of its own.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, §A.8, proof of Theorem 4, p. 44

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

namespace FastBestSubset.PSI

/-- Proof of Theorem 4 (§A.8, p. 44): a CW minimum `b` with support `S` minimizes `f` over the
vectors supported in `S`; hence any two CW minima with the same support have the same
objective `F`. -/
theorem same_objective {n p : ℕ} (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) :
    (∀ b : Fin p → ℝ, FastBestSubset.CDSS.IsCWMin D b →
        ∀ γ : Fin p → ℝ, (∀ i ∉ FastBestSubset.CDSS.supp b, γ i = 0) → FastBestSubset.CDSS.f D b ≤ FastBestSubset.CDSS.f D γ) ∧
      (∀ b b' : Fin p → ℝ, FastBestSubset.CDSS.IsCWMin D b → FastBestSubset.CDSS.IsCWMin D b' → FastBestSubset.CDSS.supp b = FastBestSubset.CDSS.supp b' → FastBestSubset.CDSS.F D b = FastBestSubset.CDSS.F D b') := by sorry

end FastBestSubset.PSI
