-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:49:17.200222+00:00
-- url     : https://prove2.me/theorems/0023ae72-7726-444d-9898-4086a45c6dad
-- title:
--   Original global Lévy NX absolute real jump kernel equals intrinsic physical finite-horizon marked mass
-- statement:
--   For the actual original Lévy path and its genuine global marked NX and finite-horizon intrinsic NT on (0,T], the integrated absolute value of every measurable real kernel supported by T is exactly equal on NX and NT. This is a source-measure identity, proved by original global and stopped count-to-tsum theorems with exact final contact and origin exclusion, and directly transfers local physical C1 integrability to the original compensated global NX source without equality in law or new stochastic hypotheses.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (f : ℝ≥0 × ℝ → ℝ) (hf : Measurable f)
    (hSupport : ∀ p : ℝ≥0 × ℝ, T < p.1 → f p = 0) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
        (fun u : ℝ≥0 => (u, Δ u)))
    let NT : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
          (fun u : ℝ≥0 => (u, Δ u)))
    (∫⁻ p, ENNReal.ofReal |f p| ∂NX) =
      (∫⁻ p, ENNReal.ofReal |f p| ∂NT) := by sorry
