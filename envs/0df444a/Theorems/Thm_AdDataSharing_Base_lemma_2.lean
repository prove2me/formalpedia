-- Prove2me | Theorems.Thm_AdDataSharing_Base_lemma_2
-- name    : AdDataSharing.Base.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:02.314672+00:00
-- url     : https://prove2.me/theorems/4bfbd644-ec3b-4307-bc29-c1ea7bd640f2
-- title:
--   Lemma 2 — if ADX1 is open, full cross-targeting is an equilibrium iff (No Leave) and (No Leave & Snipe) hold
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ allows cross-targeting. Then there is a subgame-perfect equilibrium of stages 2–3 in which both advertisers share data with $ADX_1$ (full cross-targeting) if and only if
--   $$
--   \text{(No Leave)} \quad\text{and}\quad \text{(No Leave \& Snipe)}
--   $$
--   both hold.
--
--   The lemma turns the existence of the full cross-targeting equilibrium into two explicit inequalities in the primitives.
--
--   **Formalization Note.** The equilibrium includes optimal snipe decisions for both advertisers, on and off the path; a deviating advertiser keeps its own (optimal) snipe decision.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 24, Lemma 2 (argument on pp. 8–9)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Lemma 2 (p. 24): if ADX1 is open, full cross-targeting (both advertisers on ADX1) is a
subgame-perfect equilibrium for some stage-3-optimal snipe plans if and only if both (No Leave)
and (No Leave & Snipe) hold. -/
theorem lemma_2 (P : Params) (hP : P.Standing) :
    (∃ σ : Plan × Plan, IsSPE P true σ ∧ σ.1.ex = .adx1 ∧ σ.2.ex = .adx1) ↔
      NoLeave P ∧ NoLeaveSnipe P := by sorry

end AdDataSharing.Base
