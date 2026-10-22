-- Prove2me | Theorems.Thm_BirkhoffRestrictedThreeBody_momentum_bound
-- name    : BirkhoffRestrictedThreeBody.momentum_bound
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-10T02:27:26.042205+00:00
-- url     : https://prove2.me/theorems/b0498aba-3d2a-41d5-a79c-7d2476b9e12d
-- title:
--   Lemma 4.2 — regularized momentum bound
-- statement:
--   Let $0\le\mu\le\tfrac12$ and $c\ge2.1$. On the compact component $\Sigma_{\mu,c}$ of the Levi-Civita-regularized energy hypersurface corresponding to the primary at $q=(-\mu,0)$, every state $(z_1,z_2,w_1,w_2)$ satisfies
--
--   $$
--   \sqrt{w_1^2+w_2^2}\le2.
--   $$
--
--   This a priori momentum estimate is Lemma 4.2 of Joung and van Koert. Together with the position bound, it confines the component to a fixed box used in the paper's validated convexity computation.
--
--   **Formalization Note.** The component is selected inside $K_{\mu,c}^{-1}(0)\cap\{D>0\}$ by the base point $(0,0,\sqrt{1-\mu},0)$; all parameter endpoints are included.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159, p. 19, Lemma 4.2.

import Definitions.Def_BirkhoffRestrictedThreeBody

namespace BirkhoffRestrictedThreeBody

/-- Joung--van Koert, Lemma 4.2. -/
theorem momentum_bound (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    Real.sqrt (wNormSq s) ≤ 2 := by sorry

end BirkhoffRestrictedThreeBody
