-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_full_generator_signed_ruin_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_full_generator_signed_ruin_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:28:24.555909+00:00
-- url     : https://prove2.me/theorems/c482fae5-36a9-4989-9d5c-362c5943b368
-- title:
--   Sharp original compensated upper generator residual bound including zero-landing Levy atom
-- statement:
--   The sharp genuine source compensated generator residual upper bound at any strict upper reserve retains the entire signed strict-ruin jump integral, the negative intensity of large ruin jumps, and the exact Lévy landing atom at reserve zero. All surviving negative jumps have nonpositive compensated kernel and are the only contributions discarded. Valid for zero and positive optimal caps, BV or infinite activity, without moment or atomlessness hypotheses.
-- source:
--   Original source generator above barrier, accepted exact closed ruin-region generator integral, accepted all-cap positive compensated jump kernel identity and source integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_full_generator_signed_ruin_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (∫ y in Ioo (-1 : ℝ) (-x), (-vcstar W x - y) ∂X.ν) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x + (X.ν).real ({-x} : Set ℝ) * (vcstar W 0 - vcstar W x + if x < 1 then x else 0) - q * vcstar W x := by sorry
