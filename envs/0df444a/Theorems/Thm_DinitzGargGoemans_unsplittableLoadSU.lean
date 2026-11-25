-- Prove2me | Theorems.Thm_DinitzGargGoemans_unsplittableLoadSU
-- name    : DinitzGargGoemans.unsplittableLoadSU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:47.268799+00:00
-- url     : https://prove2.me/theorems/c04003ac-d569-42c8-82fc-145d9524666c
-- title:
--   Dinitz Garg Goemans: unsplittable Load SU
-- statement:
--   The Dinitz Garg Goemans construction uses the unsplittable Load SU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L171-L178
-- source:
--   https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/blob/cc7284cf415fc2a773f00d400319ef39663c277a/DinitzGargGoemans/Proof.lean#L171-L178

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans

theorem DinitzGargGoemans.unsplittableLoadSU (q : Commodity → RouteChoice) :
    unsplittableLoad counterexampleInstance q .sU =
      (if q .one = .free then 15 else 0) +
        (if q .two = .free then 10 else 0) + 15 := by sorry
