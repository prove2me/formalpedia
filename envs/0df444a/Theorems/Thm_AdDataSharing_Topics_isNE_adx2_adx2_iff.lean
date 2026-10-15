-- Prove2me | Theorems.Thm_AdDataSharing_Topics_isNE_adx2_adx2_iff
-- name    : AdDataSharing.Topics.isNE_adx2_adx2_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:43.622443+00:00
-- url     : https://prove2.me/theorems/9ef1f594-cb02-4bbc-8e83-26d2ffd0adf5
-- title:
--   Proof of Proposition 5, pp. 29–30 — both advertisers bidding on ADX2 is an equilibrium iff $w\ge w_2$
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Then the profile in which both advertisers bid on $ADX_2$ is an equilibrium if and only if
--   $$w\ \ge\ w_2=\frac{[(1+\eta_2)-\sigma]M+\alpha\sigma C}{\tau(1+\eta_2)-\sigma(1-\alpha)} .$$
--
--   Together with the characterization of the other profiles, this pins down the region of large $\tau$ (equivalently large $w$) in which both advertisers retarget on $ADX_2$ and $ADX_1$ sells nothing.
--
--   **Formalization Note** The page says "only if $w>w_2$"; at $w=w_2$ the deviation to $ADX_1$ yields exactly the same profit, so with weak deviation inequalities the exact condition is $w\ge w_2$, which is stated.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), Appendix pp. 29–30, proof of Proposition 5, "If" part (threshold w2, p. 30)

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem isNE_adx2_adx2_iff (P : Params) (hP : P.Standing) :
    IsNE P .adx2 .adx2 ↔ w₂ P ≤ P.w := by sorry

end AdDataSharing.Topics
