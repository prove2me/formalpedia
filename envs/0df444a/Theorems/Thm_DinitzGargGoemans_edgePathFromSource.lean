-- Prove2me | Theorems.Thm_DinitzGargGoemans_edgePathFromSource
-- name    : DinitzGargGoemans.edgePathFromSource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:50:13.697971+00:00
-- url     : https://prove2.me/theorems/cab296e4-3995-517b-a8ad-eebc58fba9c5
-- title:
--   Dinitz Garg Goemans: edge Path From Source
-- statement:
--   The Dinitz Garg Goemans construction uses the edge Path From Source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L92-L110
-- source:
--   https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L92-L110

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans

theorem DinitzGargGoemans.edgePathFromSource (as : List Arc) (v : Vertex) :
    edgePath .source as v ↔
      (as = [] ∧ v = .source) ∨
      (as = [.sT1] ∧ v = .terminal1) ∨
      (as = [.sT2] ∧ v = .terminal2) ∨
      (as = [.sU] ∧ v = .junctionU) ∨
      (as = [.sU, .uV] ∧ v = .junctionV) ∨
      (as = [.sU, .uT3] ∧ v = .terminal3) ∨
      (as = [.sU, .uV, .vT1] ∧ v = .terminal1) ∨
      (as = [.sU, .uV, .vW] ∧ v = .junctionW) ∨
      (as = [.sU, .uV, .vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.sU, .uV, .vW, .wT3] ∧ v = .terminal3) := by sorry
