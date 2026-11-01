-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_nonnegative_mark_rectangle_compensator
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_nonnegative_mark_rectangle_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:59:27.599206+00:00
-- url     : https://prove2.me/theorems/ff815c22-e125-4a55-852a-9373d4168291
-- title:
--   Original Lévy intrinsic predictable rectangle compensator vanishes for nonnegative marks
-- statement:
--   For the genuine original SpectrallyNegativeLevy P 𝓕 process X, an original-filtration past event A in 𝓕_s, and any measurable B ⊆ [0,∞), the exact original-path jump-count rectangle expectation over A equals P(A)(t−s) X.ν(B). Both sides are zero: the original-path intrinsic jump measure charges no nonnegative marks pathwise, and X.ν([0,∞))=0. This verifies the nonnegative-mark branch of the source rectangle compensator target 393b03a8-2e9a-43d8-b415-854d86d58104 for every source sample space and time interval, without BV, finite intensity, Poisson replacement, conditional count laws, or filtration changes. Negative-mark intensity remains a separate obligation.
-- source:
--   Pinned source definition 933ced80-71c1-4c0f-a6a7-ab7757fc97e9 with ν_Ici=0, canonical original-path spectral support 12e84fff-dc00-4473-8213-068484f459ae; direct positive-mark subcase of open compensator 393b03a8-2e9a-43d8-b415-854d86d58104.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_nonnegative_mark_rectangle_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBnonneg : B ⊆ Ici (0 : ℝ)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
