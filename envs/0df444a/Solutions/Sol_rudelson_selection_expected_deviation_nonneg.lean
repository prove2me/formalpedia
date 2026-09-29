-- Prove2me | solution 1 for rudelson_selection_expected_deviation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:42:11.254823+00:00
-- url     : https://prove2.me/submissions/5256b224-148b-46e0-be7d-a547fb915e33

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 1000000

theorem solution {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) {p : Real} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliExpectation p (fun Omega => tangentSamplingDeviation Omega S p) := by
  unfold bernoulliExpectation
  apply Finset.sum_nonneg
  intro Omega _
  refine mul_nonneg ?_ ?_
  · -- weight nonneg for 0 ≤ p ≤ 1
    unfold bernoulliObservationWeight
    refine mul_nonneg (pow_nonneg hp0 _) (pow_nonneg ?_ _)
    linarith
  · -- pointwise nonneg of the deviation sSup, for 0 ≤ p
    unfold tangentSamplingDeviation
    apply Real.sSup_nonneg
    intro v hv
    obtain ⟨X, _, _, hveq⟩ := hv
    rw [hveq]
    exact mul_nonneg (inv_nonneg.mpr hp0) (Real.sqrt_nonneg _)
