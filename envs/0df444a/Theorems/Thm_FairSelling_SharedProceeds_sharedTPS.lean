-- Prove2me | Theorems.Thm_FairSelling_SharedProceeds_sharedTPS
-- name    : FairSelling.SharedProceeds.sharedTPS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:55:52.728989+00:00
-- url     : https://prove2.me/theorems/9ace7dfe-f9d1-4a3f-a746-8834add29c3c
-- title:
--   Shared Proceeds: shared TPS
-- statement:
--   The truncated proportional share of each agent is `13/2`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L65-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L65-L77

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds

theorem FairSelling.SharedProceeds.sharedTPS : TPS 2 sv sp = 13 / 2 := by sorry
