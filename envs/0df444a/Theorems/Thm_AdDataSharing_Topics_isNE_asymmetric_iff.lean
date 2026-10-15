-- Prove2me | Theorems.Thm_AdDataSharing_Topics_isNE_asymmetric_iff
-- name    : AdDataSharing.Topics.isNE_asymmetric_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:43.887838+00:00
-- url     : https://prove2.me/theorems/3b99fe71-5f36-4fb5-b415-ab999967fc48
-- title:
--   Proof of Proposition 5, p. 30 — an asymmetric profile is an equilibrium iff $w_1\le w\le w_2$
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Then each asymmetric profile — one advertiser bids on $ADX_1$, the other on $ADX_2$, in either order — is an equilibrium if and only if
--   $$w_1\le w\le w_2,$$
--   where
--   $$w_1=\frac{(1+\eta_2)-\sigma(1-\alpha)}{\tau(1+\eta_2)-\sigma(1-\alpha)}\,C,\qquad w_2=\frac{[(1+\eta_2)-\sigma]M+\alpha\sigma C}{\tau(1+\eta_2)-\sigma(1-\alpha)}.$$
--
--   The advertiser on $ADX_1$ does not deviate exactly when $w\le w_2$, and the advertiser on $ADX_2$ does not deviate exactly when $w\ge w_1$.
--
--   **Formalization Note** The page states only the "if" direction ("asymmetric strategies do not exhibit a profitable unilateral deviation if $w_1\le w\le w_2$"); the equivalence holds and is stated, for both orders of the two advertisers.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), Appendix p. 30, proof of Proposition 5 (asymmetric strategies, w1 ≤ w ≤ w2)

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem isNE_asymmetric_iff (P : Params) (hP : P.Standing) :
    (IsNE P .adx1 .adx2 ↔ w₁ P ≤ P.w ∧ P.w ≤ w₂ P) ∧
      (IsNE P .adx2 .adx1 ↔ w₁ P ≤ P.w ∧ P.w ≤ w₂ P) := by sorry

end AdDataSharing.Topics
