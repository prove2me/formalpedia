-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
-- name    : AvramDividend.Classical.avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:25:00.667897+00:00
-- url     : https://prove2.me/theorems/3e5bbc19-2879-4eeb-96dd-bdde918dbb1b
-- title:
--   Original Lévy square-energy makes all negative mark sets separated from zero finite intensity
-- statement:
--   For any genuine Lévy mark measure with the exact Lévy quadratic condition, and any threshold 0<δ≤1, the negative tail (-∞,-δ] has finite mass. Construct the strictly positive energy threshold δ² via elementary real inequalities, apply the already proved positive-energy finite-intensity lemma. This is required for BV C1 original-source large-jump L1 integrability and avoids assuming a Poisson-copy measure.
-- source:
--   Source-specific companion to avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity, supplied original physical Lévy intensity ν and exact min(1,z²) Lévy energy.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
    (ν : Measure ℝ)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂ν) < ⊤)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ν (Iic (-δ)) < ⊤ := by sorry
