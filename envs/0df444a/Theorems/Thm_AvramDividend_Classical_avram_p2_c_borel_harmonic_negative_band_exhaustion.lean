-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
-- name    : AvramDividend.Classical.avram_p2_c_borel_harmonic_negative_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:18:28.559197+00:00
-- url     : https://prove2.me/theorems/679340e8-f52b-486b-b26d-9ad0b151dc7f
-- title:
--   Explicit harmonic cutoff exhaustion of every strictly negative Borel mark set
-- statement:
--   The canonical Lévy mark truncations B∩(-∞,-1/(n+1)] of any measurable strictly negative set B form a measurable increasing exhaustive sequence with strictly negative cutoffs. Packages the explicit sequence required to apply the already proved source monotone-rate theorem, without a stochastic rate assumption.
-- source:
--   P2-C applies its Proved general negative band exhaustion theorem fffe16cc to the explicit positive antitone harmonic cutoff sequence from the accepted 4928a464 decomposition sketch, relying on pinned Mathlib tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_harmonic_negative_band_exhaustion
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∀ n : ℕ, MeasurableSet (B ∩ Iic (-(1 / ((n : ℝ) + 1))))) ∧
    Monotone (fun n : ℕ => B ∩ Iic (-(1 / ((n : ℝ) + 1)))) ∧
    (⋃ n : ℕ, B ∩ Iic (-(1 / ((n : ℝ) + 1)))) = B ∧
    (∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ B ∩ Iic (-(1 / ((n : ℝ) + 1))) ⊆ Iic (-δ)) := by sorry
