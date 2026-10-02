-- Prove2me | solution 1 for isSimplyConnected_unitDisc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T20:24:15.706445+00:00
-- url     : https://prove2.me/submissions/a66fe59c-5fc8-43cb-98bc-2fc64f9748f3

import Mathlib

open Set

/-- The open unit disc is a ball, hence contractible; a contractible space is simply
connected.  The contractibility has to be *installed* as an instance, because
`IsSimplyConnected` is a plain `def` for a class and the elaborator will not run
instance search on a bare term of the wrong head type. -/
theorem solution : IsSimplyConnected (Metric.ball 0 1 : Set ℂ) := by
  haveI : ContractibleSpace (Metric.ball 0 1 : Set ℂ) :=
    Metric.contractibleSpace_ball (r := 1) (by norm_num)
  exact SimplyConnectedSpace.ofContractible _
