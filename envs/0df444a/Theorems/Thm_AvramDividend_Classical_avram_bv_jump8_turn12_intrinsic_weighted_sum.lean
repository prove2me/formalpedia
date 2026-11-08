-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_intrinsic_weighted_sum
-- name    : AvramDividend.Classical.avram_bv_jump8_turn12_intrinsic_weighted_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:19:35.857367+00:00
-- url     : https://prove2.me/theorems/977c6028-d9ef-4b63-8e17-be00eb351757
-- title:
--   Original strict intrinsic marked loss equals its literal finite ENNReal weighted sum
-- statement:
--   For the actual original spectrally negative Levy process and its strict negative finite-mark set, the (0,T] intrinsic Borel-weighted marked integral agrees with the literal ENNReal finite sum, retaining the zero-origin exclusion and strict magnitude cutoff.
-- source:
--   Adapt Proved original weighted finite-sum identity 35828b50 via lintegral over the product restriction Ioc 0 T ×ˢ univ and Borel negative-mark indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn12_intrinsic_weighted_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    ∀ ω : Ω,
      (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ u ∈ S ω, ENNReal.ofReal
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
