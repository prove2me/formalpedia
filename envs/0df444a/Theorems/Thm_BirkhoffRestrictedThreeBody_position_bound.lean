-- Prove2me | Theorems.Thm_BirkhoffRestrictedThreeBody_position_bound
-- name    : BirkhoffRestrictedThreeBody.position_bound
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-10T02:27:12.481262+00:00
-- url     : https://prove2.me/theorems/8485120a-b851-4fcb-8b9e-5d6bfb1d3a9b
-- title:
--   Lemma 4.1 — regularized position bound
-- statement:
--   Let $0\le\mu\le\tfrac12$ and $c\ge2.1$. On the compact component $\Sigma_{\mu,c}$ of the Levi-Civita-regularized energy hypersurface corresponding to the primary at $q=(-\mu,0)$, every state $(z_1,z_2,w_1,w_2)$ satisfies
--
--   $$
--   2(z_1^2+z_2^2)\le\frac35.
--   $$
--
--   Equivalently, the regularized position coordinate remains in the disk of squared radius $3/10$. This a priori estimate is the “in particular” conclusion of Lemma 4.1 and is used to confine the component before checking its curvature.
--
--   **Formalization Note.** The component is selected inside $K_{\mu,c}^{-1}(0)\cap\{D>0\}$ by the base point $(0,0,\sqrt{1-\mu},0)$; all parameter endpoints are included.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159, p. 19, Lemma 4.1 (in particular clause).

import Definitions.Def_BirkhoffRestrictedThreeBody

namespace BirkhoffRestrictedThreeBody

/-- The `2|z|² ≤ 3/5` consequence of Joung--van Koert, Lemma 4.1. -/
theorem position_bound (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    2 * zNormSq s ≤ 3 / 5 := by sorry

end BirkhoffRestrictedThreeBody
