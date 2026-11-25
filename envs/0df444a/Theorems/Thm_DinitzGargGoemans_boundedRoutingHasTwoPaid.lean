-- Prove2me | Theorems.Thm_DinitzGargGoemans_boundedRoutingHasTwoPaid
-- name    : DinitzGargGoemans.boundedRoutingHasTwoPaid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:54:03.978739+00:00
-- url     : https://prove2.me/theorems/933b70bc-c541-4f6f-8bd0-fd6febf917e5
-- title:
--   Dinitz Garg Goemans: bounded Routing Has Two Paid
-- statement:
--   The Dinitz Garg Goemans construction uses the bounded Routing Has Two Paid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L206-L220
-- source:
--   https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L206-L220

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans

theorem DinitzGargGoemans.boundedRoutingHasTwoPaid (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    2 ≤ paidCount q := by sorry
