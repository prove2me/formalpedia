-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_deterministic_compensator_mass_bound
-- name    : AvramDividend.Classical.avram_ja19_original_smallband_deterministic_compensator_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:58:38.037976+00:00
-- url     : https://prove2.me/theorems/818ef8ff-641e-49ff-bdfe-68e936e417d9
-- title:
--   Finite negative Levy mass bounds the original small-band deterministic compensator
-- statement:
--   For a finite negative Levy measure, the deterministic drift compensation over the band (-1,-1/(k+1)] has absolute value at most t times the total mass of all negative marks because each mark in this band has |z|≤1. With t≤T this is at most T times the total negative Levy mass. Use set-integral absolute-value and finite-measure monotonicity; no large-jump moment assumption.
-- source:
--   J-A19 deterministic Levy compensator bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_smallband_deterministic_compensator_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (T : ℝ≥0) (k : ℕ) (t : ℝ≥0), t ≤ T →
      |(t : ℝ) * (∫ z in Ioc (-1 : ℝ)
          (-(1 / ((k : ℝ) + 1))), z ∂X.ν)| ≤
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
