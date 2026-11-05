-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:28:01.126232+00:00
-- url     : https://prove2.me/theorems/52ba6ff9-c369-434d-b463-2e9ad9b2f63c
-- title:
--   Original nonnegative compact-negative intrinsic jump sum has exact ENNReal Lévy first moment
-- statement:
--   For the genuine original spectrally negative Lévy process and a nonnegative compactly supported negative test g, exhibit the integrable finite original jump-mark sum J, prove J is pathwise nonnegative, and identify its ENNReal expected first moment with ENNReal.ofReal of the original T times ν test integral. This transports an already-proved real Bochner expected sum to an exact positive extended-real identity, retaining original sample space and original X.ν.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_compact_negative_jump_mean

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ))))) := by sorry
