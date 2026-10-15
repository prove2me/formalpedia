-- Prove2me | Theorems.Thm_AdDataSharing_Base_proposition_1
-- name    : AdDataSharing.Base.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:06.062466+00:00
-- url     : https://prove2.me/theorems/fade3340-b00f-4f2c-ae7e-e20b4df20e70
-- title:
--   Proposition 1 — ADX1 allows cross-targeting iff (No Leave & Snipe) and (No Leave) hold; both advertisers always contract with ADX1
-- statement:
--   Assume the standing assumptions $0<\alpha<\tfrac12$, $0<w<C<M<2C$, $0<\varphi<1$, $0<\eta_1<\eta_2$. Then the game has an equilibrium (subgame-perfect, in pure strategies, with Assumption 1 applied in each stage-2 subgame), and every equilibrium has the following properties.
--   1. If $ADX_1$ allows cross-targeting, then (No Leave & Snipe) and (No Leave) both hold.
--   2. If (No Leave & Snipe) and (No Leave) both hold, and neither holds with equality, then $ADX_1$ allows cross-targeting.
--   3. On the equilibrium path both advertisers share data with $ADX_1$, and each targets the look-alike audience of size $\eta_2$.
--
--   In short, off the knife edge,
--   $$
--   ADX_1 \text{ allows cross-targeting} \iff \text{(No Leave \& Snipe)} \wedge \text{(No Leave)} ,
--   $$
--   in which case both advertisers cross-target, and both advertisers always contract with $ADX_1$ and retarget their exclusive visitors.
--
--   The proposition explains how an ad exchange's data-sharing policy can block cross-targeting even when advertisers would gain from it: $ADX_1$ always secures both advertisers' data, but it keeps cross-targeting closed whenever opening would drive one of them to $ADX_2$.
--
--   **Formalization Note.** Under an open $ADX_1$ with both advertisers on it, the model's payoff is full cross-targeting, display (2), so "both advertisers cross-target" is part of clause 3; retargeting one's own visitors is built into every plan. The no-equality hypothesis in clause 2 is an addition: when the binding condition holds with equality, the open subgame also has an equilibrium with one advertiser on each exchange and the same advertiser payoffs, Assumption 1 does not remove it, and it gives $ADX_1$ less than staying closed, so an equilibrium with $ADX_1$ closed exists although both conditions hold (exhibited in the mission's sanity file). $C>w$ is a disclosed standing assumption (footnote 3, p. 5; p. 21).
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 9, Proposition 1 (proof pp. 27–28)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Proposition 1 (p. 9): an equilibrium of the whole game exists, and in every equilibrium
(1) if ADX1 allows cross-targeting then (No Leave & Snipe) and (No Leave) both hold;
(2) if (No Leave & Snipe) and (No Leave) both hold, ADX1 allows cross-targeting (corrected: off
    the knife edge where one of them holds with equality);
(3) both advertisers contract with ADX1 on the equilibrium path, and each targets the look-alike
    audience of size `η₂`. Under an open ADX1 this is full cross-targeting, payoff (2). -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∃ x : Outcome, IsEquilibrium P x) ∧
      ∀ x : Outcome, IsEquilibrium P x →
        (x.isOpen = true → NoLeaveSnipe P ∧ NoLeave P) ∧
        (NoLeaveSnipe P ∧ NoLeave P → NoKnifeEdge P → x.isOpen = true) ∧
        x.path.1.ex = .adx1 ∧ x.path.2.ex = .adx1 ∧
        lookAlike P x.path.1 x.path.2 = P.η₂ := by sorry

end AdDataSharing.Base
