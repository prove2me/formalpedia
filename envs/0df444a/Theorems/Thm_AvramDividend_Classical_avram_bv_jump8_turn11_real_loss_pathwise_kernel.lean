-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_real_loss_pathwise_kernel
-- name    : AvramDividend.Classical.avram_bv_jump8_turn11_real_loss_pathwise_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:06:03.817139+00:00
-- url     : https://prove2.me/theorems/718373d7-72e3-4f87-88b9-475a82a602c2
-- title:
--   Actual strict original marked-loss finite sum equals the intrinsic pathwise ENNReal integral
-- statement:
--   On the actual source Levy path, finite strict negative marks on (0,T] have a nonnegative real loss whose ENNReal image equals the corresponding intrinsic marked kernel lintegral, using the Proved source-exact Borel weighted finite-sum result 35828b50 and no independent PRM.
-- source:
--   Source-exact original strict negative marked finite Borel weighted finite-sum identity Proved 35828b50; real ofReal sum conversion with finite strict time support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn11_real_loss_pathwise_kernel
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
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    ∀ ω : Ω, 0 ≤ L ω ∧
      (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ENNReal.ofReal (L ω) := by sorry
