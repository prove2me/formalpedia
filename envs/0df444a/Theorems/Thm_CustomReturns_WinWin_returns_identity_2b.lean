-- Prove2me | Theorems.Thm_CustomReturns_WinWin_returns_identity_2b
-- name    : CustomReturns.WinWin.returns_identity_2b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:59.914988+00:00
-- url     : https://prove2.me/theorems/65ba6246-5836-48af-a2ee-fc69e7623d8b
-- title:
--   Return-volume identity for Solutions 2 and 2b
-- statement:
--   In the Solution 2/2b region, with $r_s<r_s^{SB2}(r_c)$ to exclude the corner, let $R_{\mathrm{tot}}^2$ and $R_{\mathrm{tot}}^{2b}$ be the total returns calculated from the respective closed-form segment sizes. Define $W=m_s(1-m_c)-m_c(1-m_s)(1-\beta_c)$. Then
--
--   $$
--   R_{\mathrm{tot}}^2-R_{\mathrm{tot}}^{2b}
--   =\frac{(1-m_s)(r_s^{SB2}(r_c)-r_s)W}
--          {2m_s[m_s-(1-\beta_c)m_c]},
--   \qquad
--   R_{\mathrm{tot}}^2<R_{\mathrm{tot}}^{2b}\iff W<0.
--   $$
--
--   The identity isolates the condition under which permitting customized returns reduces the firm's total number of returns.
--
--   **Formalization Note** The identity uses the exact rational expressions from Appendix A.2 and Table 6. It is checked symbolically and at the rational witness. The hypotheses retain the Solution 2/2b region in which the paper interprets those expressions as sales segments.
-- source:
--   Esenduran, Letizia & Ovchinnikov, Customization and Returns, accepted manuscript (Management Science, accepted Dec. 13, 2021; SSRN 3444244), proof of Proposition 2, Online Appendix p. 15 (PDF 31), comparison (i); Table 6, Online Appendix p. 5 (PDF 21)

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

namespace CustomReturns.WinWin

/-- Identity (i) in the comparison of Solutions 2 and 2b,
proof of Proposition 2, Online Appendix p. 15. -/
theorem returns_identity_2b (P : Params)
    (hstanding : P.Standing) (hθ : 0 < P.θ) (hβ : P.βc < 1)
    (hregionS : P.rs ≤ P.θ) (hregionC : rbarbar_c P ≤ P.rc)
    (hcase : rSB1 P ≤ P.rs) (hstrict : P.rs < rSB2 P) :
    (1 - P.ms) * QRs2 P + (1 - P.mc) * QRc2 P - (1 - P.ms) * QRs2b P =
      (1 - P.ms) * (rSB2 P - P.rs) * W P /
        (2 * P.ms * (P.ms - (1 - P.βc) * P.mc)) ∧
    ((1 - P.ms) * QRs2 P + (1 - P.mc) * QRc2 P - (1 - P.ms) * QRs2b P < 0 ↔
      W P < 0) := by sorry

end CustomReturns.WinWin
