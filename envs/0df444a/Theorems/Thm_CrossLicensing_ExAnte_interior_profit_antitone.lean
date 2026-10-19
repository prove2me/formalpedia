-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_interior_profit_antitone
-- name    : CrossLicensing.ExAnte.interior_profit_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:34.813495+00:00
-- url     : https://prove2.me/theorems/afd60972-5d3c-4691-a036-38a3e9cb9317
-- title:
--   Proof of Proposition 4(ii), p. A.2 — interior supplier profit decreases with k₂
-- statement:
--   Fix $k_1>49/144$ and $0\le\beta\le1$. Within the feasible interior-duopoly cost region $49/144<k_2<k_1$ and $\hat k_2(k_1\mid\beta)\le k_2$, the printed supplier profit $\pi_s^I(\beta)$ strictly falls as $k_2$ increases:
--
--   $$k_2<k_2'\quad\Longrightarrow\quad\pi_s^I(\beta;k_1,k_2')<\pi_s^I(\beta;k_1,k_2).$$
--
--   This monotonicity supplies the single-crossing comparison with the boundary profit without cross-licensing, which does not depend on $k_2$.
--
--   **Formalization Note** This item covers the $k_2$ half of the appendix's two-variable monotonicity sentence. Its domain is the part used for case (ii); the optional $k_1$ half is outside this mission.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. A.2 (PDF 34), proof of Proposition 4(ii), monotonicity paragraph

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- The k₂ half of the monotonicity assertion in the proof of Proposition
4(ii), p. A.2, restricted to the feasible interior-duopoly regime. -/
theorem interior_profit_antitone (k1 β : ℝ)
    (hk1 : (49 : ℝ) / 144 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    StrictAntiOn (fun k2 : ℝ => piInterior β k1 k2)
      {k2 : ℝ | (49 : ℝ) / 144 < k2 ∧ k2 < k1 ∧ khat2 k1 β ≤ k2} := by sorry

end CrossLicensing.ExAnte
