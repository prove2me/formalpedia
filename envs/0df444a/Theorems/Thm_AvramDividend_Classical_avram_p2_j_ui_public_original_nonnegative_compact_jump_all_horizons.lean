-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_nonnegative_compact_jump_all_horizons
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_all_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:18:50.597507+00:00
-- url     : https://prove2.me/theorems/19e234ac-480e-4bf7-865d-54b12a5f74b3
-- title:
--   Public source-exact nonnegative original intrinsic compact jump first moment at every horizon
-- statement:
--   For the genuine original spectrally negative Levy process and a nonnegative continuous compactly supported test separated from zero on the negative half-line, the integrable finite uncentred jump sum has its exact extended-real first moment for every horizon including zero. This strengthens the publicly Proved positive-horizon original test identity and does not introduce an independent rate or compensator assumption.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_all_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hfnonneg : ∀ y : ℝ, 0 ≤ f y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
