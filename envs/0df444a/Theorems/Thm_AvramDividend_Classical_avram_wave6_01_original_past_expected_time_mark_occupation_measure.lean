-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_expected_time_mark_occupation_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:13:44.566025+00:00
-- url     : https://prove2.me/theorems/e509ef60-0d03-429a-a727-37c8bc8f1865
-- title:
--   The original Lévy past-restricted jump expectation is a genuine time–mark measure
-- statement:
--   For the same original Ω,P,𝓕 and X.X, and each actual past event A∈𝓕_s, there is a measure Q_A on physical time × real jump marks such that Q_A(C) is the expected literal intrinsic source jump count in every jointly Borel time–mark set C over A. It is the genuine Campbell occupation measure (P.restrict A).bind κ for the canonically Proved source s-finite kernel, not a guessed du⊗ν compensator, nor a proxy Poisson random measure. This completes the exact measure-level domain needed for nonnegative predictable simple-step sums, leaving identification of Q_A on source rectangles against P(A)du ν(dy) as the primary positive-rate obligation.
-- source:
--   Canonical Proved actual s-finite jump kernel eb357d08, Measure.bind_apply and exact pointwise source kernel identity; unrestricted Borel C in original time–mark space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_expected_time_mark_occupation_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ Q : Measure (ℝ≥0 × ℝ), ∀ C : Set (ℝ≥0 × ℝ),
      MeasurableSet C →
      Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by sorry
