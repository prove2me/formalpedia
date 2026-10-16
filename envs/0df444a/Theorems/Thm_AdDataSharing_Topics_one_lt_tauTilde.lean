-- Prove2me | Theorems.Thm_AdDataSharing_Topics_one_lt_tauTilde
-- name    : AdDataSharing.Topics.one_lt_tauTilde
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:36.40439+00:00
-- url     : https://prove2.me/theorems/5a7c5819-a8aa-44c3-a8e5-963457ee5214
-- title:
--   Proof of Proposition 5, p. 30 — the corrected threshold satisfies $\tilde\tau>1$
-- statement:
--   Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Then the accuracy threshold of Proposition 5 exceeds one:
--   $$\tilde\tau=\frac{(1+\eta_2)-\sigma(1-\alpha)}{w(1+\eta_2)}\,C+\frac{\sigma(1-\alpha)}{1+\eta_2}\ >\ 1 .$$
--
--   So the region $1<\tau<\tilde\tau$ in which both advertisers bid on $ADX_1$ is never empty: a Topics system that is slightly imprecise is always used.
--
--   **Formalization Note** $\tilde\tau$ is the corrected threshold (the printed (6) lacks the factor $1/(1+\eta_2)$ on its first term). The page's argument cites "$C<w$", a slip for the standing assumption $C>w$.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), Appendix p. 30, last sentence of the proof of Proposition 5 (τ̃ > 1; threshold corrected)

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem one_lt_tauTilde (P : Params) (hP : P.Standing) : 1 < tauTilde P := by sorry

end AdDataSharing.Topics
