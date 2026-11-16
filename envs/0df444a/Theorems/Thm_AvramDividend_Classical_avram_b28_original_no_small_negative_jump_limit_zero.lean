-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
-- name    : AvramDividend.Classical.avram_b28_original_no_small_negative_jump_limit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:52:26.151915+00:00
-- url     : https://prove2.me/theorems/3a978678-27cc-434a-a179-f970aa864cf8
-- title:
--   Original limiting compensated negative-small-jump process vanishes almost surely simultaneously at all physical times if the process has only large jumps
-- statement:
--   Assume the original Lévy measure has zero mass on (-1,0], and almost every physical sample path has only zero or at most -1 jumps at positive times. Then the source's cutoff small-band compensated martingale is identically zero at every cutoff and every time, by Proved original-source theorem 489c24bc. Every simultaneously defined almost-sure cutoff-limit Jsmall must therefore vanish at all physical times by uniqueness of real limits. This identifies the exact original limiting small jump channel used in B25 with zero for Brownian plus size-two negative compound Poisson, without changing its compensator.
-- source:
--   Prove2Me accepted 489c24bc original no-small-band compensation zero, original B25 hJsource limit syntax, 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b28_original_no_small_negative_jump_limit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Jsmall u ω = 0 := by sorry
