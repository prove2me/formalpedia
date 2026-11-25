-- Prove2me | Theorems.Thm_Arxiv1810_02867_convolution_reciprocity
-- name    : Arxiv1810_02867.convolution_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:21:50.7728+00:00
-- url     : https://prove2.me/theorems/164beab8-acf3-53ec-a40a-524366f6edad
-- title:
--   Eq. (11): general reciprocity theorem of the convolution type
-- statement:
--   Let $\mathbb D$ be a bounded domain in the $(x_1,x_3)$-plane with boundary $\partial\mathbb D$ and outward unit normal $\mathbf n=(n_1,n_3)$, on which the theorem of Gauss holds. Let $\omega\in\mathbb R$. Consider two states $A$ and $B$, each with $C^1$ fields $P,Q_r$, continuous sources $B,C_r$ and continuous real parameters $\alpha,\beta_{rs},\gamma_r$ with $\beta_{rs}=\beta_{sr}$. Suppose both states satisfy the frequency-domain equations (8)-(9) in $\mathbb D$:
--   $$-i\omega\alpha P+(\partial_r-i\omega\gamma_r)Q_r=B,\qquad (\partial_r-i\omega\gamma_r)P-i\omega\beta_{rs}Q_s=C_r.$$
--   Then
--   $$\oint_{\partial\mathbb D}(P_AQ_{r,B}-Q_{r,A}P_B)n_r\,\mathrm d\mathbf x=i\omega\int_{\mathbb D}\big((\alpha_B-\alpha_A)P_AP_B-(\beta_{rs,B}-\beta_{rs,A})Q_{r,A}Q_{s,B}\big)\mathrm d\mathbf x$$
--   $$+\,i\omega\int_{\mathbb D}(\gamma_{r,B}+\gamma_{r,A})(P_AQ_{r,B}-Q_{r,A}P_B)\,\mathrm d\mathbf x+\int_{\mathbb D}(C_{r,A}Q_{r,B}-Q_{r,A}C_{r,B}+P_AB_B-B_AP_B)\,\mathrm d\mathbf x.$$
--
--   This is the general reciprocity theorem of the convolution type. Because $\gamma$ enters as $\gamma_{r,A}+\gamma_{r,B}$, the $\gamma$ integral does not vanish for two states in the same non-reciprocal medium.
--
--   **Formalization Note** The domain is given with a boundary measure and a unit normal for which Gauss's theorem holds for every $C^1$ field. Every bounded Lipschitz domain with arc length and outward normal is an example. The paper leaves the smoothness implicit. The $C^1$ fields and continuous sources and parameters are the standing convention that makes every integral finite.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c003; Section III, eqs. (7)-(11), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem convolution_reciprocity (ω : ℝ) (G : GaussDomain) (SA SB : FreqState)
    (hA : FreqEqs ω SA G.D) (hB : FreqEqs ω SB G.D) (hregA : SA.Regular) (hregB : SB.Regular)
    (hsymA : ∀ x r s, SA.beta x r s = SA.beta x s r)
    (hsymB : ∀ x r s, SB.beta x r s = SB.beta x s r) :
    ∫ x, ∑ r, (SA.P x * SB.Q x r - SA.Q x r * SB.P x) * (G.normal x r : ℂ) ∂G.sigma =
      Complex.I * ω * ∫ x in G.D, (((SB.alpha x - SA.alpha x : ℝ) : ℂ) * SA.P x * SB.P x -
          ∑ r, ∑ s, ((SB.beta x r s - SA.beta x r s : ℝ) : ℂ) * SA.Q x r * SB.Q x s) +
      Complex.I * ω * ∫ x in G.D, ∑ r, ((SB.gamma x r + SA.gamma x r : ℝ) : ℂ) *
          (SA.P x * SB.Q x r - SA.Q x r * SB.P x) +
      ∫ x in G.D, (∑ r, (SA.C x r * SB.Q x r - SA.Q x r * SB.C x r) +
          SA.P x * SB.B x - SA.B x * SB.P x) := by sorry

end Arxiv1810_02867
