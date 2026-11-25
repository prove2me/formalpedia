-- Prove2me | Theorems.Thm_Arxiv1810_02867_correlation_reciprocity
-- name    : Arxiv1810_02867.correlation_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:22:55.270512+00:00
-- url     : https://prove2.me/theorems/59073a44-623a-5056-8efa-41b8e66e0090
-- title:
--   Eq. (15): general reciprocity theorem of the correlation type
-- statement:
--   In the setting of the convolution-type theorem (two states with $C^1$ fields, continuous sources and continuous real parameters with $\beta_{rs}=\beta_{sr}$, satisfying (8)-(9) in a Gauss domain $\mathbb D$, $\omega\in\mathbb R$), with $^*$ denoting complex conjugation, eq. (15) holds:
--   $$\oint_{\partial\mathbb D}(P_A^*Q_{r,B}+Q_{r,A}^*P_B)n_r\,\mathrm d\mathbf x=i\omega\int_{\mathbb D}\big((\alpha_B-\alpha_A)P_A^*P_B+(\beta_{rs,B}-\beta_{rs,A})Q_{r,A}^*Q_{s,B}\big)\mathrm d\mathbf x$$
--   $$+\,i\omega\int_{\mathbb D}(\gamma_{r,B}-\gamma_{r,A})(P_A^*Q_{r,B}+Q_{r,A}^*P_B)\,\mathrm d\mathbf x+\int_{\mathbb D}(C_{r,A}^*Q_{r,B}+Q_{r,A}^*C_{r,B}+P_A^*B_B+B_A^*P_B)\,\mathrm d\mathbf x.$$
--
--   This is the general reciprocity theorem of the correlation type. Real (lossless) parameters are essential, since the conjugated equation of state $A$ is used.
--
--   **Formalization Note** The formalization conventions are those of the convolution-type theorem.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c006; Section III, eqs. (14)-(15), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem correlation_reciprocity (ω : ℝ) (G : GaussDomain) (SA SB : FreqState)
    (hA : FreqEqs ω SA G.D) (hB : FreqEqs ω SB G.D) (hregA : SA.Regular) (hregB : SB.Regular)
    (hsymA : ∀ x r s, SA.beta x r s = SA.beta x s r)
    (hsymB : ∀ x r s, SB.beta x r s = SB.beta x s r) :
    ∫ x, ∑ r, (starRingEnd ℂ (SA.P x) * SB.Q x r + starRingEnd ℂ (SA.Q x r) * SB.P x) *
        (G.normal x r : ℂ) ∂G.sigma =
      Complex.I * ω * ∫ x in G.D, (((SB.alpha x - SA.alpha x : ℝ) : ℂ) * starRingEnd ℂ (SA.P x) *
          SB.P x + ∑ r, ∑ s, ((SB.beta x r s - SA.beta x r s : ℝ) : ℂ) *
            starRingEnd ℂ (SA.Q x r) * SB.Q x s) +
      Complex.I * ω * ∫ x in G.D, ∑ r, ((SB.gamma x r - SA.gamma x r : ℝ) : ℂ) *
          (starRingEnd ℂ (SA.P x) * SB.Q x r + starRingEnd ℂ (SA.Q x r) * SB.P x) +
      ∫ x in G.D, (∑ r, (starRingEnd ℂ (SA.C x r) * SB.Q x r + starRingEnd ℂ (SA.Q x r) * SB.C x r) +
          starRingEnd ℂ (SA.P x) * SB.B x + starRingEnd ℂ (SA.B x) * SB.P x) := by sorry

end Arxiv1810_02867
