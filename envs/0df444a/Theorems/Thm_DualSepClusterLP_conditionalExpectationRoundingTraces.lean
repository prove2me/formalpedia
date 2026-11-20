-- Prove2me | Theorems.Thm_DualSepClusterLP_conditionalExpectationRoundingTraces
-- name    : DualSepClusterLP.conditionalExpectationRoundingTraces
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T07:55:37.993047+00:00
-- url     : https://prove2.me/theorems/d89d8f14-8628-407a-892a-893212e59629
-- title:
--   Appendix F — deterministic execution of two rounding procedures
-- statement:
--   Given a feasible explicit sparse rational cluster-LP solution, assume the cluster-based rule admits a positive-weight progressing choice of nonnegative margin on each nonempty alive set and that the conditional-affine pivot rule has nonnegative expected margin on every alive set. A single deterministic finite-alphabet machine, running in polynomial time in the explicit bit length of the input, outputs the cheaper of two clusterings. In each of these clusterings the labels specify the removal rounds, and in each round the total pair budget released covers the disagreements incurred. The trace guarantees use the cluster-based budgets for the first clustering and the pivot budgets for the second. The ratio bound and the validity of the variance certificate are consequences established separately.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper 79, Appendix F, Proposition F.1, using the one-round expressions of §7.1–7.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Definitions.Def_DualSepClusterLP_SparseInput
import Definitions.Def_DualSepClusterLP_RoundingAnalysis

namespace DualSepClusterLP

/-- Implement the two conditional-expectation procedures in Appendix F.
The hypotheses certify the existence of a nonincreasing step on each alive set.
The output encodes the cheaper of the two constructed partitions. -/
theorem conditionalExpectationRoundingTraces :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (n : ℕ) (G : Graph n) (L : SparseWeights n), ValidSupport L →
        let z := fun S => (weightAt L S : ℝ)
        ClockStepOK G z → PivotStepOK G z →
        ∃ C P : Clustering n,
          RoundTraceOK G C z clusterEdgeBudget ∧ RoundTraceOK G P z pivotEdgeBudget ∧
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((roundingInput G L).map M.inputAlphabet.symm)
            (some ((partitionOutput
              (if disagreements G C ≤ disagreements G P then C else P)).map M.outputAlphabet.symm))
            (A * ((roundingInput G L).length + 1)^b)) := by sorry

end DualSepClusterLP
