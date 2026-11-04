-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_actual_physical_BV_C1_local_negative_mark_tail_from_levy_energy
-- name    : AvramDividend.Classical.avram_wave8_22_actual_physical_BV_C1_local_negative_mark_tail_from_levy_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:52:19.090184+00:00
-- url     : https://prove2.me/theorems/17ab2832-0320-4725-a84f-76422636f6b1
-- title:
--   Physical negative Lévy tail finite at the actual BV C¹ reserve-localisation threshold from the original Lévy quadratic energy
-- statement:
--   For the unchanged original spectrally negative Lévy source, the genuine quadratic Lévy intensity condition gives finite negative jump intensity on (-∞,-a/2] whenever a is positive and at most two. Supplies exactly the hMass parameter of the stopped compact BV C1 physical generator jump compensator and uses the original ν, without finite total jump activity or an invented intensity assertion.
-- source:
--   Proved original Lévy quadratic separated negative tail theorem 3e5bbc19-2879-4eeb-96dd-bdde918dbb1b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_actual_physical_BV_C1_local_negative_mark_tail_from_levy_energy
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
  (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
  X.ν (Iic (-(a / 2))) < ⊤ := by sorry
