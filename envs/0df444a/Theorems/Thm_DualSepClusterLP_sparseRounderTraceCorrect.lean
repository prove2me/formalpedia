-- Prove2me | Theorems.Thm_DualSepClusterLP_sparseRounderTraceCorrect
-- name    : DualSepClusterLP.sparseRounderTraceCorrect
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T13:31:47.656887+00:00
-- url     : https://prove2.me/theorems/ff4db312-a1f3-4cba-b915-6d288e0fbe91
-- title:
--   Correctness of the two executable conditional-expectation rounders
-- statement:
--   For a feasible explicit rational cluster LP solution satisfying the clock and pivot step bounds, the executable word function outputs the cheaper of two partitions. Every round of each partition covers its disagreements from the corresponding released edge budgets.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Appendix F (conditional-expectation rounding), https://arxiv.org/abs/2607.27829.

import Definitions.Def_DualSepClusterLP_SparseRounder

namespace DualSepClusterLP

theorem sparseRounderTraceCorrect {n : ℕ} (G : Graph n) (L : SparseWeights n)
    (hL : ValidSupport L) (hc : ClockStepOK G (fun S => (weightAt L S : ℝ)))
    (hp : PivotStepOK G (fun S => (weightAt L S : ℝ))) :
    ∃ C P : Clustering n,
      RoundTraceOK G C (fun S => (weightAt L S : ℝ)) clusterEdgeBudget ∧
      RoundTraceOK G P (fun S => (weightAt L S : ℝ)) pivotEdgeBudget ∧
      RoundWire.output (roundingInput G L) =
        partitionOutput (if disagreements G C ≤ disagreements G P then C else P) := by sorry

end DualSepClusterLP
