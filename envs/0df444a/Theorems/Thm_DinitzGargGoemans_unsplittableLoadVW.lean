-- Prove2me | Theorems.Thm_DinitzGargGoemans_unsplittableLoadVW
-- name    : DinitzGargGoemans.unsplittableLoadVW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:42.844927+00:00
-- url     : https://prove2.me/theorems/305c6247-07e2-4d23-a95d-3c83b1a7696d
-- title:
--   Dinitz Garg Goemans: unsplittable Load VW
-- statement:
--   The Dinitz Garg Goemans construction uses the unsplittable Load VW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L190-L196
-- source:
--   https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L190-L196

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans

theorem DinitzGargGoemans.unsplittableLoadVW (q : Commodity → RouteChoice) :
    unsplittableLoad counterexampleInstance q .vW =
      (if q .two = .free then 10 else 0) +
        (if q .three = .free then 15 else 0) := by sorry
