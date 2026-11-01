-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_generator_residual_le_overshoot
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_generator_residual_le_overshoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:48:43.08352+00:00
-- url     : https://prove2.me/theorems/39fc6d37-6e8c-443c-94c3-85bd5734b248
-- title:
--   Unconditional original source generator residual upper bound by exact ruin-crossing overshoot
-- statement:
--   For every strict reserve above either a positive or zero optimal barrier, unconditionally bound the original compensated Levy generator residual by drift plus the exactly integrable small-ruin overshoot correction minus discount. Includes genuine generator-domain integrability, Gaussian affine simplification and crossing-zero boundary under source assumptions without extra jump moments.
-- source:
--   Source above-cap generator equality, source-only overshoot integrability, and all-cap exact compensated positive-part identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_generator_residual_le_overshoot {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) - q * vcstar W x := by sorry
