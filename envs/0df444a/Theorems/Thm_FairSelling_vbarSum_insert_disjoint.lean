-- Prove2me | Theorems.Thm_FairSelling_vbarSum_insert_disjoint
-- name    : FairSelling.vbarSum_insert_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:15.200315+00:00
-- url     : https://prove2.me/theorems/401adf9a-a351-4a20-8891-946624d55aca
-- title:
--   Fair Selling: vbar Sum insert disjoint
-- statement:
--   The value of the removed set `K ∪ {f}`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L56-L59
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L56-L59

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.vbarSum_insert_disjoint (w p : G → ℝ) (K : Finset G) (f : G) (hfK : f ∉ K) :
    vbarSum w p (K ∪ {f}) = vbarSum w p K + vbar w p f := by sorry
