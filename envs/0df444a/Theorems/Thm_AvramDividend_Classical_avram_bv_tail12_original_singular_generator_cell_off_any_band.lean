-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_singular_generator_cell_off_any_band
-- name    : AvramDividend.Classical.avram_bv_tail12_original_singular_generator_cell_off_any_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:59:02.434192+00:00
-- url     : https://prove2.me/theorems/9fe384d7-9b8c-486e-ac39-a115ac14cf69
-- title:
--   Original singular BV Levy generator has arbitrarily negative sampled cells below every compact band
-- statement:
--   For the actual original bounded variation spectrally negative Levy generator with singular negative jump density and compensated drift zero, and for each positive compact band edge, find a literal positive surplus outside the band at which the actual generator minus the affine one-discount candidate has arbitrarily negative physical grid-cell contribution. This is conditional on the original Levy process.
-- source:
--   Source-bound original generator identification from public Proved 24cc445a and deterministic real-surplus cell theorem public Proved 68d97f1d. This isolates the literal signed B generator-term validity gap in canonical 0b2da5b3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_actual_reserve_outside_any_band_deficit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_original_singular_generator_cell_off_any_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ y : ℝ, 0 < y ∧ y < a / 2 ∧ y < 1 ∧
      (1 / ((K : ℝ) + 4)) *
        (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
          (1 + y)) ≤ -(K : ℝ) := by sorry
