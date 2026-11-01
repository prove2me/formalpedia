-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_jump_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_signed_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:09:29.081591+00:00
-- url     : https://prove2.me/theorems/93ab7fe0-cac5-4388-9e26-8e8a7bacfc09
-- title:
--   Signed compensated source Levy jump bound retaining finite large-ruin killing
-- statement:
--   For the genuine source compensated Lévy generator of the barrier candidate at all strict upper reserves, the compensated negative-jump kernel is bounded by the small-ruin overshoot minus the full barrier value on the disjoint large-ruin jump strip. This retains the negative killing contribution lost in a positive-part bound, handles zero cap and possible landing atoms, and requires no extra Lévy moment hypothesis.
-- source:
--   The original source generatorIntegrand and established all-cap positive-part jump theorem, plus barrierValue zero at strict negative reserves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_signed_jump_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (y : ℝ) (hy : y < 0) : SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ (if y ∈ Ioo (-1 : ℝ) (-x) then max 0 (-vcstar W x - y) else 0) - (if y ∈ Iic (-1 : ℝ) ∩ Iio (-x) then vcstar W x else 0) := by sorry
