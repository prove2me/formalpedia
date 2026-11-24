-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exGoodOutcome_TPS_SEFX
-- name    : FairSelling.TPSSefxCounterexample.exGoodOutcome_TPS_SEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:40:22.398169+00:00
-- url     : https://prove2.me/theorems/b850a545-3ee4-4986-aeaa-9198463efe2f
-- title:
--   TPSSefx Counterexample: ex Good Outcome TPS SEFX
-- statement:
--   **The instance is not a counterexample to Theorem 2**: it admits an outcome that is envy
--   free — hence SEFX — and gives both agents `30 ≥ (2/3)·TPS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L274-L289
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L274-L289

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample

theorem FairSelling.TPSSefxCounterexample.exGoodOutcome_TPS_SEFX :
    exGoodOutcome.Valid exp ∧
      (∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exGoodOutcome i) ∧
      SEFX exV exp exGoodOutcome := by sorry
