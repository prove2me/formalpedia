-- Prove2me | Theorems.Thm_AdDataSharing_Base_lemma_3
-- name    : AdDataSharing.Base.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:09.183095+00:00
-- url     : https://prove2.me/theorems/7daa5361-9b2e-427a-a62d-edf1f128f6b1
-- title:
--   Lemma 3 (corrected) — if full cross-targeting is an equilibrium, no other equilibrium has an advertiser on ADX1
-- statement:
--   Assume the standing assumptions, suppose $ADX_1$ allows cross-targeting, and suppose full cross-targeting is a subgame-perfect equilibrium of stages 2–3. Assume moreover that neither (No Leave) nor (No Leave & Snipe) holds with equality. Then every subgame-perfect equilibrium $\sigma$ in which at least one advertiser shares data with $ADX_1$ satisfies
--   $$
--   \sigma_1 \text{ and } \sigma_2 \text{ both share data with } ADX_1 ,
--   $$
--   so it is full cross-targeting.
--
--   Together with Lemma 4 this lets Assumption 1 select full cross-targeting whenever it is an equilibrium.
--
--   **Formalization Note.** The hypothesis that neither condition binds is an addition. The paper's proof calls the deviation of the advertiser on $ADX_2$ profitable when (3) $\le$ (2) or (4) $\le$ (2); it is profitable only under strict inequality. When the relevant condition holds with equality, the profile with one advertiser on each exchange is an equilibrium with the same payoffs (exhibited in the mission's sanity file), and the lemma as printed is false.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 25, Lemma 3

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Lemma 3 (p. 25): if ADX1 is open and full cross-targeting is an equilibrium, every
equilibrium in which at least one advertiser contracts with ADX1 has both advertisers on ADX1.
Corrected: stated off the knife edge where (No Leave) or (No Leave & Snipe) holds with equality;
there an asymmetric equilibrium with the same payoffs exists. -/
theorem lemma_3 (P : Params) (hP : P.Standing) (hk : NoKnifeEdge P)
    (hfull : ∃ σ₀ : Plan × Plan, IsSPE P true σ₀ ∧ σ₀.1.ex = .adx1 ∧ σ₀.2.ex = .adx1)
    (σ : Plan × Plan) (hσ : IsSPE P true σ) (hone : σ.1.ex = .adx1 ∨ σ.2.ex = .adx1) :
    σ.1.ex = .adx1 ∧ σ.2.ex = .adx1 := by sorry

end AdDataSharing.Base
