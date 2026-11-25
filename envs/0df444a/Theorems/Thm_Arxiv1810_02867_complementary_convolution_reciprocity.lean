-- Prove2me | Theorems.Thm_Arxiv1810_02867_complementary_convolution_reciprocity
-- name    : Arxiv1810_02867.complementary_convolution_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:22:32.562879+00:00
-- url     : https://prove2.me/theorems/89e093b1-78ad-4495-b24d-f2975acb965f
-- title:
--   Eq. (12): convolution-type reciprocity theorem for a medium and its complementary version
-- statement:
--   In the setting of the convolution-type theorem, let state $B$ be in the actual medium with parameters $\alpha,\beta_{rs},\gamma_r$. Let state $A$ be in the complementary medium, with parameters $\alpha,\beta_{rs},-\gamma_r$. Then the medium-dependent integrals vanish and (12) holds:
--   $$\oint_{\partial\mathbb D}(P^{(c)}_AQ_{r,B}-Q^{(c)}_{r,A}P_B)n_r\,\mathrm d\mathbf x=\int_{\mathbb D}(C^{(c)}_{r,A}Q_{r,B}-Q^{(c)}_{r,A}C_{r,B}+P^{(c)}_AB_B-B^{(c)}_AP_B)\,\mathrm d\mathbf x.$$
--
--   This theorem relates wave fields in a non-reciprocal medium to wave fields in its complementary version. It is the basis of the paper's Green's function representations.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c004; Section III, eq. (12), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem complementary_convolution_reciprocity (ω : ℝ) (G : GaussDomain) (SA SB : FreqState)
    (hA : FreqEqs ω SA G.D) (hB : FreqEqs ω SB G.D) (hregA : SA.Regular) (hregB : SB.Regular)
    (hsym : ∀ x r s, SB.beta x r s = SB.beta x s r)
    (halpha : SA.alpha = SB.alpha) (hbeta : SA.beta = SB.beta)
    (hgamma : SA.gamma = fun x r => -SB.gamma x r) :
    ∫ x, ∑ r, (SA.P x * SB.Q x r - SA.Q x r * SB.P x) * (G.normal x r : ℂ) ∂G.sigma =
      ∫ x in G.D, (∑ r, (SA.C x r * SB.Q x r - SA.Q x r * SB.C x r) +
          SA.P x * SB.B x - SA.B x * SB.P x) := by sorry

end Arxiv1810_02867
