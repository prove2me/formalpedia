-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_landing_atom_integral_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_landing_atom_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:17:59.27674+00:00
-- url     : https://prove2.me/theorems/73d8f0b9-c5e6-4a30-9d00-8d8322f91551
-- title:
--   Exact source Levy generator crossing integral including zero-reserve landing atom
-- statement:
--   An exact original-source generator integral formula over all jumps crossing to or below reserve zero, with the signed strict-ruin compensation integral and negative large-ruin intensity plus the explicit Lévy atom at the jump landing exactly on zero. The landing atom coefficient retains v(0) and the source small-jump compensation convention at x=1, covering bounded variation models rigorously.
-- source:
--   Original generatorIntegrand with indicator (-1,1), derivative one above cstar, source generator integrability, and exact strict-ruin signed jump integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_landing_atom_integral_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ (∫ y in Iic (-x), SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) = (∫ y in Ioo (-1 : ℝ) (-x), (-vcstar W x - y) ∂X.ν) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x + (X.ν).real ({-x} : Set ℝ) * (vcstar W 0 - vcstar W x + if x < 1 then x else 0) := by sorry
