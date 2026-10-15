-- Prove2me | Theorems.Thm_AdDataSharing_Topics_w1_lt_w2
-- name    : AdDataSharing.Topics.w1_lt_w2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:53.25675+00:00
-- url     : https://prove2.me/theorems/21428638-046f-44e4-8341-5967e80c4fbe
-- title:
--   Proof of Proposition 5, p. 30 — $w_2>w_1$
-- statement:
--   Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Then the two thresholds of the Topics bidding game satisfy
--   $$w_1=\frac{(1+\eta_2)-\sigma(1-\alpha)}{\tau(1+\eta_2)-\sigma(1-\alpha)}\,C\ <\ \frac{[(1+\eta_2)-\sigma]M+\alpha\sigma C}{\tau(1+\eta_2)-\sigma(1-\alpha)}=w_2 .$$
--
--   Because $w_1<w_2$, the regions where both advertisers bid on $ADX_1$ ($w\le w_1$) and where both bid on $ADX_2$ ($w\ge w_2$) are disjoint, which gives the uniqueness part of Proposition 5.
--
--   **Formalization Note** The page's displayed decomposition of $w_2$ omits a factor $C$ on its first term; the stated inequality $w_2>w_1$ is the page's conclusion and does not depend on that display.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), Appendix p. 30, proof of Proposition 5 (w2 > w1)

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem w1_lt_w2 (P : Params) (hP : P.Standing) : w₁ P < w₂ P := by sorry

end AdDataSharing.Topics
