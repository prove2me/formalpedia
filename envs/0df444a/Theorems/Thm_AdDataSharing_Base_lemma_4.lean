-- Prove2me | Theorems.Thm_AdDataSharing_Base_lemma_4
-- name    : AdDataSharing.Base.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:06.431044+00:00
-- url     : https://prove2.me/theorems/17e26d60-e96f-4e5c-9ecb-287a61db484b
-- title:
--   Lemma 4 (corrected) — full cross-targeting strictly Pareto-dominates every other equilibrium for advertisers
-- statement:
--   Assume the standing assumptions, suppose $ADX_1$ allows cross-targeting, and assume that neither (No Leave) nor (No Leave & Snipe) holds with equality. Let $\sigma$ be a subgame-perfect equilibrium of stages 2–3 with both advertisers on $ADX_1$, and let $\sigma'$ be a subgame-perfect equilibrium in which not both advertisers are on $ADX_1$. Then
--   $$
--   u_i(\sigma') < u_i(\sigma)\qquad\text{for both advertisers } i=1,2 ,
--   $$
--   that is, $\sigma$ strictly Pareto-dominates $\sigma'$ for the advertisers.
--
--   Under Assumption 1 this removes every equilibrium other than full cross-targeting.
--
--   **Formalization Note.** The comparison is with equilibria whose exchange profile differs; two full cross-targeting profiles that differ only in an off-path snipe decision have equal payoffs. The no-equality hypothesis is an addition (see Lemma 3): at the knife edge an asymmetric equilibrium has the same payoffs as full cross-targeting.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 25, Lemma 4

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Lemma 4 (p. 25): if ADX1 is open and full cross-targeting is an equilibrium, it strictly
Pareto-dominates, for the advertisers, every equilibrium whose exchange profile is not full
cross-targeting. Corrected: stated off the knife edge where (No Leave) or (No Leave & Snipe)
holds with equality; there an asymmetric equilibrium with the same payoffs exists. -/
theorem lemma_4 (P : Params) (hP : P.Standing) (hk : NoKnifeEdge P)
    (σ : Plan × Plan) (hσ : IsSPE P true σ) (h₁ : σ.1.ex = .adx1) (h₂ : σ.2.ex = .adx1)
    (σ' : Plan × Plan) (hσ' : IsSPE P true σ')
    (hother : ¬ (σ'.1.ex = .adx1 ∧ σ'.2.ex = .adx1)) :
    ParetoDominates P true σ σ' := by sorry

end AdDataSharing.Base
