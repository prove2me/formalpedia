-- Prove2me | Theorems.Thm_Arxiv1810_02867_same_medium_correlation_reciprocity
-- name    : Arxiv1810_02867.same_medium_correlation_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:23:36.663615+00:00
-- url     : https://prove2.me/theorems/28f3a77d-af20-4631-bd3e-6d60ab11dc12
-- title:
--   Eq. (16): correlation-type reciprocity theorem in one medium
-- statement:
--   In the setting of the correlation-type theorem, let the parameters $\alpha,\beta_{rs},\gamma_r$ be identical in states $A$ and $B$. Then eq. (16) holds:
--   $$\oint_{\partial\mathbb D}(P_A^*Q_{r,B}+Q_{r,A}^*P_B)n_r\,\mathrm d\mathbf x=\int_{\mathbb D}(C_{r,A}^*Q_{r,B}+Q_{r,A}^*C_{r,B}+P_A^*B_B+B_A^*P_B)\,\mathrm d\mathbf x.$$
--
--   Unlike the convolution type, the correlation-type theorem needs no complementary medium: both states are in the actual medium.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c007; Section III, eq. (16), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem same_medium_correlation_reciprocity (ω : ℝ) (G : GaussDomain) (SA SB : FreqState)
    (hA : FreqEqs ω SA G.D) (hB : FreqEqs ω SB G.D) (hregA : SA.Regular) (hregB : SB.Regular)
    (hsym : ∀ x r s, SB.beta x r s = SB.beta x s r)
    (halpha : SA.alpha = SB.alpha) (hbeta : SA.beta = SB.beta) (hgamma : SA.gamma = SB.gamma) :
    ∫ x, ∑ r, (starRingEnd ℂ (SA.P x) * SB.Q x r + starRingEnd ℂ (SA.Q x r) * SB.P x) *
        (G.normal x r : ℂ) ∂G.sigma =
      ∫ x in G.D, (∑ r, (starRingEnd ℂ (SA.C x r) * SB.Q x r + starRingEnd ℂ (SA.Q x r) * SB.C x r) +
          starRingEnd ℂ (SA.P x) * SB.B x + starRingEnd ℂ (SA.B x) * SB.P x) := by sorry

end Arxiv1810_02867
