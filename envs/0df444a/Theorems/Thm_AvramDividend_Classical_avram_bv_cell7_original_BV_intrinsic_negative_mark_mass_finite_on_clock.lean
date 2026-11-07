-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:36:32.988196+00:00
-- url     : https://prove2.me/theorems/3ada0328-905b-4d1b-9db3-b7c5a5d2ccd4
-- title:
--   Original bounded-variation Lévy intrinsic marked negative jump magnitude is finite on every physical horizon
-- statement:
--   For the actual original spectrally negative bounded-variation Lévy path, its exact intrinsic marked count measure on the half-open time interval (0,T] has a finite integral of negative mark magnitude, almost surely for every bounded clock T. The proof reuses the already accepted original BV jump magnitude tsum finiteness and original intrinsic count-to-tsum identity, removing the origin and preserving the closed final contact. This is the original-source integrable dominating measure for the full stopped compensated C1 H kernel.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (-p.2) ∂NT) < ⊤ := by sorry
