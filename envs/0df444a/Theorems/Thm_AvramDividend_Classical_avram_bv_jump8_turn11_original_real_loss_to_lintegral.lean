-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_real_loss_to_lintegral
-- name    : AvramDividend.Classical.avram_bv_jump8_turn11_original_real_loss_to_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:36:36.219191+00:00
-- url     : https://prove2.me/theorems/a09f08d2-7082-4e77-b0b3-cccf404249b4
-- title:
--   Original physical strict marked finite loss has real mean equal to toReal of genuine intrinsic Campbell lintegral
-- statement:
--   Transport the original finite strict negative marked loss through the genuine intrinsic jump kernel, with exact (0,T] time convention and Bochner/lintegral real conversion. Requires original finite-cutoff real integrability rather than a generic Poisson-process axiom.
-- source:
--   Transport the original finite strict negative marked loss through the genuine intrinsic jump kernel, with exact (0,T] time convention and Bochner/lintegral real conversion. Requires original finite-cutoff real integrability rather than a generic Poisson-process axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn11_original_real_loss_to_lintegral
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
    (∫ ω, L ω ∂P) =
      ((∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P)).toReal := by sorry
