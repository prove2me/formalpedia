-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixedTPS_one_ge
-- name    : FairSelling.MixedGood.mixedTPS_one_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:44.990577+00:00
-- url     : https://prove2.me/theorems/902e9bd7-d53e-41df-8ef2-124b7ac8d8a1
-- title:
--   Mixed Good: mixed TPS one ge
-- statement:
--   Agent `1` has a truncated proportional share of at least `12`: `t = 12` is a fixed point of
--   the truncated-proportional map, `(12 + 6 + 6)/2 = 12`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L84-L90
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L84-L90

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixedTPS_one_ge : (12 : ℝ) ≤ TPS 2 (mv 1) mp := by sorry
