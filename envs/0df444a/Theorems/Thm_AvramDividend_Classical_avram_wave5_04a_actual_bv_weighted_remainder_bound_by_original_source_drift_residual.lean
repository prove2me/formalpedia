-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:23:37.518314+00:00
-- url     : https://prove2.me/theorems/ae763e15-49e9-4dd0-b1b2-4168ba7d0c52
-- title:
--   Actual BV source residual weighted partition variation dominated by observable drift-minus-source increment
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, almost surely its canonical explicit downward residual after all intrinsic negative original left jumps has every weighted ordered-partition sum bounded in absolute value by the coefficient sup bound M times the source drift-minus-actual-path endpoint increment. This bound removes the unobserved residual R from the right-hand side and supplies a source-only pathwise envelope useful for future expectation and C1 limit arguments. No pure-jump equality, independent Poisson model or controlled Ito-Meyer identity is assumed.
-- source:
--   Chat04-A source envelope derived by combining canonically Proved exact original-source drift/intrinsic-jumps/residual interval theorem c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and Proved exact weighted residual total variation 2496fb55-e8d1-455f-9cea-0728d868c5b9; residual witnesses coincide by definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Weighted BV source-remainder partition sums are bounded directly
by the actual source drift-minus-process increment, with no residual
remaining on the right-hand side; useful for moment envelopes. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by sorry
