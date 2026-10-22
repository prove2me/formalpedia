-- Prove2me | Theorems.Thm_AdDataSharing_Topics_isNE_adx1_adx1_iff
-- name    : AdDataSharing.Topics.isNE_adx1_adx1_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:33.588392+00:00
-- url     : https://prove2.me/theorems/8de01530-97fd-4c63-a414-448411bda85a
-- title:
--   Proof of Proposition 5, p. 29 — both advertisers bidding on ADX1 is an equilibrium iff $w\le w_1$, iff $\tau\le\tilde\tau$
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Then the profile in which both advertisers bid on $ADX_1$ is an equilibrium if and only if
--   $$w\le \frac{(1+\eta_2)-\sigma(1-\alpha)}{\tau(1+\eta_2)-\sigma(1-\alpha)}\,C,$$
--   and, equivalently, if and only if
--   $$\tau\le \frac{(1+\eta_2)-\sigma(1-\alpha)}{w(1+\eta_2)}\,C+\frac{\sigma(1-\alpha)}{1+\eta_2}.$$
--
--   This is the "only if" step of the proof of Proposition 5: the only deviation from $(ADX_1,ADX_1)$ is to $ADX_2$, which yields $\sigma(1-\alpha)(C-w)$ instead of $(1+\eta_2)(C-\tau w)$.
--
--   **Formalization Note** The page writes the sufficient condition $w<w_1$; the exact condition, with weak deviation inequalities, is $w\le w_1$, and that is stated. The $\tau$-form uses the corrected threshold $\tilde\tau$; the page's conversion "$w<w_1\Leftrightarrow\tau<\dots$" omits the factor $1/(1+\eta_2)$ on the first term.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), Appendix p. 29, proof of Proposition 5, "Only if" part (threshold w1; τ-form corrected)

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem isNE_adx1_adx1_iff (P : Params) (hP : P.Standing) :
    (IsNE P .adx1 .adx1 ↔ P.w ≤ w₁ P) ∧ (IsNE P .adx1 .adx1 ↔ P.τ ≤ tauTilde P) := by sorry

end AdDataSharing.Topics
