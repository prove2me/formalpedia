-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_arbitrator_standard
-- name    : CurbEmissions.ExactStandard.arbitrator_standard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:21.974003+00:00
-- url     : https://prove2.me/theorems/49d901d8-bca0-4789-9d37-1dd669fbdab3
-- title:
--   §3.2, p. 16, eq. (3) — the arbitrator's optimal standard is s∗a = (2h1[ū+b(c−γ)]−(c−γ)ū)/((c−γ)[4h1−(c−γ)])
-- statement:
--   Let the standing assumptions hold. A neutral arbitrator sets one standard $s_a\ge0$ for both markets to maximize
--   $$\pi_a(s_a)=\frac{m_1+m_2}{8\bar u}[\bar u-(c-\gamma)s_a]^2-h_1(b-s_a)\frac{m_1+m_2}{2\bar u}[\bar u-(c-\gamma)s_a].$$
--   Then
--   $$s^*_a=\frac{2h_1[\bar u+b(c-\gamma)]-(c-\gamma)\bar u}{(c-\gamma)[4h_1-(c-\gamma)]}$$
--   is nonnegative, and $\pi_a(s_a)<\pi_a(s^*_a)$ for every $s_a\ge0$ with $s_a\neq s^*_a$.
--
--   The arbitrator's problem coincides with the maximization of the regulators' total utility under an exact global standard, so $s^*_a$ is the candidate negotiated standard $s^*_e$ of Proposition 3.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 16, §3.2, eq. (3)

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- §3.2, p. 16, eq. (3): `s∗a ≥ 0` is the unique maximizer of the arbitrator's objective `π_a` over
`s_a ≥ 0`. -/
theorem arbitrator_standard (P : Params) (hP : Standing P) :
    0 ≤ saStar P ∧ ∀ sa, 0 ≤ sa → sa ≠ saStar P → piA P sa < piA P (saStar P) := by sorry

end CurbEmissions.ExactStandard
