-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_lemma_6
-- name    : AdaptiveStepIPM.Probabilistic.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:20.871214+00:00
-- url     : https://prove2.me/theorems/71664345-f90c-4bf5-bc9d-04273b09c2d3
-- title:
--   Lemma 6 — beta radial coordinate and uniform spherical direction
-- statement:
--   Fix integers $n\ge2$, $d,m\ge1$ with $d+m=n$, and an orthogonal frame $F=[g,H]$ in $\mathbb R^n$. Sample the $m\times n$ standard Gaussian matrix $G$, set $U=\ker G$, and project $r=2g$ onto $U$ to obtain $p$. Define $\zeta=\langle p,g\rangle-1$, $\eta=\sqrt{1-\zeta^2}$, and let $v$ be the normalized $H$-coordinate of $p$. Then, almost surely,
--
--   $$
--   p=(1+\zeta)g+\eta Hv,\qquad
--   \frac{1+\zeta}{2}\sim\operatorname{Beta}(d/2,m/2),\qquad
--   v\sim\operatorname{Unif}(S^{n-2}).
--   $$
--
--   The beta and spherical marginal laws are asserted separately; no independence is claimed. The decomposition supplies the geometric variables used to bound the componentwise product of the two projections.
--
--   **Formalization Note** The Gaussian null-space model represents the invariant random $d$-subspace. Measurability of both random variables is part of the conclusion. The direction is assigned zero only when its defining coordinate vanishes, a null event under $d,m\ge1$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 14, Lemma 6, Eq. (17); https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Mizuno–Todd–Ye, Lemma 6, including both marginal laws. -/
theorem lemma_6 {n d m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hdm : d + m = n) (F : Frame n) :
    AEMeasurable (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2)
      (gaussianMatrix m n) ∧
    AEMeasurable (fun G : Fin m → Fin n → ℝ => v F G)
      (gaussianMatrix m n) ∧
    (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => (1 + zeta F G) / 2) =
      betaMeasure ((d : ℝ) / 2) ((m : ℝ) / 2) ∧
    (gaussianMatrix m n).map (fun G : Fin m → Fin n → ℝ => v F G) =
      sphereGaussian (n - 1) ∧
    (∀ᵐ G ∂gaussianMatrix m n,
      p m n G (2 • F.g) =
        (1 + zeta F G) • F.g + (eta F G) • F.H (v F G) ∧
      eta F G = Real.sqrt (1 - zeta F G ^ 2) ∧
      ‖v F G‖ = 1) := by sorry

end AdaptiveStepIPM.Probabilistic
