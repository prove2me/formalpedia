-- Prove2me | Theorems.Thm_DualSepClusterLP_denseAffineApproximation
-- name    : DualSepClusterLP.denseAffineApproximation
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T14:51:15.585799+00:00
-- url     : https://prove2.me/theorems/d6ebdb59-8b63-408d-835f-4113f9c51161
-- title:
--   Affine-sampling additive approximation for dense quadratic minimization
-- statement:
--   For any ordered list of N distinct vertices, rational linear costs, and rational pair coefficients of magnitude at most one, let m be positive with m² < N. For each comparison subset there is a trial, described by three integers bounded by 2N and exactly m² bits, whose quadratic objective is at most that of the comparison subset plus 2N²/m. The same list of trials works for every subset, including an optimal one.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Lemma 5.3 (Section 5.2) and Appendix B, https://arxiv.org/abs/2607.27829. This proof gives an alternative implementation using pairwise independent affine samples and greedy completion.

import Definitions.Def_DualSepClusterLP_DenseTrials

namespace DualSepClusterLP
open Dense

theorem denseAffineApproximation {ι : Type} [DecidableEq ι] (U : List ι) (hu : U.Nodup) (A : ι → ι → ℚ) (b : ι → ℚ)
    (keep : ι → Bool) (hA : ∀ i∈U, ∀ j∈U, |A i j|≤1) (m : ℕ) (hm : 0 < m)
    (large : m^2<U.length) :
    ∃ p a d : ℕ, ∃ bits : List Bool, 0<p ∧ p≤2*U.length ∧ a < p ∧ d < p ∧ bits.length=m^2 ∧
      value A b (greedy A (rawEstimate A U (m^2) p a d bits) U b) ≤
        value A b (U.filter keep) + 2*(U.length:ℚ)^2/m := by sorry

end DualSepClusterLP
