-- Prove2me | Theorems.Thm_AdDataSharing_Topics_proposition_7_i
-- name    : AdDataSharing.Topics.proposition_7_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:29.385984+00:00
-- url     : https://prove2.me/theorems/bbe2c6a3-1705-45cc-8216-ee9a7e197405
-- title:
--   Proposition 7 (i) — for $\tau<\tau'<\tilde\tau$, ADX1's equilibrium revenue is strictly larger at $\tau'$
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Let $\tau<\tau'<\tilde\tau$, where $\tilde\tau$ is the (corrected) threshold of Proposition 5, and compare the Topics model with inaccuracy $\tau$ to the same model with inaccuracy $\tau'$ (all other parameters unchanged). Then both models have an equilibrium, and for every equilibrium $(x,y)$ at $\tau$ and every equilibrium $(x',y')$ at $\tau'$,
--   $$R_\tau(x,y)\ <\ R_{\tau'}(x',y'),$$
--   where $R$ denotes ADX1's revenue ($\varphi w$ per impression sold on $ADX_1$).
--
--   In the region where both advertisers bid on $ADX_1$, the exchange therefore profits from making the Topics system less accurate.
--
--   **Formalization Note** "ADX1's profits" is read as its revenue in equilibrium; the existence clauses rule out a vacuous comparison. $\tilde\tau$ does not depend on $\tau$, so the region $\tau<\tilde\tau$ is the same for both models.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 19, Proposition 7 (i); proof Appendix p. 30

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem proposition_7_i (P : Params) (hP : P.Standing) (τ' : ℝ) (hτ : P.τ < τ')
    (hτ' : τ' < tauTilde P) :
    (∃ x y : AdDataSharing.Base.Exchange, IsNE P x y) ∧ (∃ x y : AdDataSharing.Base.Exchange, IsNE { P with τ := τ' } x y) ∧
      ∀ x y x' y' : AdDataSharing.Base.Exchange, IsNE P x y → IsNE { P with τ := τ' } x' y' →
        revenue P x y < revenue { P with τ := τ' } x' y' := by sorry

end AdDataSharing.Topics
