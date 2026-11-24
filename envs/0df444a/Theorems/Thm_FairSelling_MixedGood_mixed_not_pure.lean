-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixed_not_pure
-- name    : FairSelling.MixedGood.mixed_not_pure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:20.776434+00:00
-- url     : https://prove2.me/theorems/df871be8-2792-4014-b7c2-0c758606af95
-- title:
--   Mixed Good: mixed not pure
-- statement:
--   **No good is pure**: agent `1` values every good, after truncation at its own truncated
--   proportional share, strictly above its market price, so selling it loses agent `1` something.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L121-L131
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L121-L131

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixed_not_pure (g : Fin 3) : ¬ PhaseTPS.PureGood mv mp (∅ : Finset (Fin 2)) g := by sorry
