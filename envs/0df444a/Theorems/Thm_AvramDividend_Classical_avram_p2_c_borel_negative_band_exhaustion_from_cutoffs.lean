-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
-- name    : AvramDividend.Classical.avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:04:44.331197+00:00
-- url     : https://prove2.me/theorems/fffe16cc-198e-458f-a6b8-1da63e33c388
-- title:
--   General monotone exhaustion of negative Borel marks by strictly separated bands
-- statement:
--   For any measurable set of strictly negative real marks and any positive nonincreasing sequence of cutoffs tending to zero, the intersection with the lower halfline at each negative cutoff is Borel, increases with the cutoff index, and exhausts the original set. Each band remains uniformly separated from zero. The statement is independent of stochastic processes or ν rates.
-- source:
--   P2-C extracted the standalone set-theoretic exhaustion subproof from existing accepted canonical 4928a464 sketch; uses Mathlib tendsto/negative order and Borel measurability. No original rate assumption.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n)
    (hεAnti : Antitone ε)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    (∀ n, MeasurableSet (B ∩ Iic (-(ε n)))) ∧
    Monotone (fun n => B ∩ Iic (-(ε n))) ∧
    (⋃ n, B ∩ Iic (-(ε n))) = B ∧
    (∀ n, ∃ δ : ℝ, 0 < δ ∧ B ∩ Iic (-(ε n)) ⊆ Iic (-δ)) := by sorry
