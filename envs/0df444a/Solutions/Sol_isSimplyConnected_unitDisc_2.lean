-- Prove2me | solution 2 for isSimplyConnected_unitDisc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T20:24:34.622223+00:00
-- url     : https://prove2.me/submissions/369aeef7-dec3-4075-b523-57451e08e794

import Mathlib

open Set

/-- The open unit disc is simply connected, because it is contractible. -/
theorem solution : IsSimplyConnected (Metric.ball 0 1 : Set ℂ) := by
  haveI hc : ContractibleSpace (Metric.ball 0 1 : Set ℂ) :=
    Metric.contractibleSpace_ball (r := 1) (by norm_num)
  show SimplyConnectedSpace (Metric.ball 0 1 : Set ℂ)
  exact SimplyConnectedSpace.ofContractible (Metric.ball 0 1)
