-- Prove2me | Theorems.Thm_FairSelling_lemmaFourCashSold_holds
-- name    : FairSelling.lemmaFourCashSold_holds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:09.503159+00:00
-- url     : https://prove2.me/theorems/c9135a01-1cec-48ca-91b1-6e6d85064773
-- title:
--   Fair Selling: lemma Four Cash Sold holds
-- statement:
--   **The residual case of Lemma 4 holds.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L217-L219
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L217-L219

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.lemmaFourCashSold_holds : LemmaFourCashSold G := by sorry
