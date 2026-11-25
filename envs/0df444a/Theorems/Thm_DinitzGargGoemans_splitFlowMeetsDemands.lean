-- Prove2me | Theorems.Thm_DinitzGargGoemans_splitFlowMeetsDemands
-- name    : DinitzGargGoemans.splitFlowMeetsDemands
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:50:33.828591+00:00
-- url     : https://prove2.me/theorems/17cbbd13-73f1-4274-bcbe-ec546d8d68b3
-- title:
--   Dinitz Garg Goemans: split Flow Meets Demands
-- statement:
--   The Dinitz Garg Goemans construction uses the split Flow Meets Demands property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L150-L154
-- source:
--   https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L150-L154

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans

theorem DinitzGargGoemans.splitFlowMeetsDemands :
    ∀ k, (∑ r, splitFlow k r) = demandAmount k := by sorry
