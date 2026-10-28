-- Prove2me | Theorems.Thm_AvramDividend_Classical_sigmaFinite_absolutelyContinuous_has_real_density
-- name    : AvramDividend.Classical.sigmaFinite_absolutelyContinuous_has_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:51:46.966465+00:00
-- url     : https://prove2.me/theorems/dfe9f2a6-57df-4780-bf98-9d336faaf753
-- title:
--   Every sigma-finite absolutely continuous real measure admits a measurable nonnegative real density
-- statement:
--   For any sigma-finite Borel measure on the real line that is absolutely continuous with respect to Lebesgue measure, construct a measurable nonnegative real function K whose ENNReal density reproduces the original measure. This supplies the real-valued Esscher renewal kernel density for the bounded-variation Avram dividend scale-function argument once the discounted jump-tail measure is known to be finite and absolutely continuous.
-- source:
--   Mathlib MeasureTheory.Measure.Decomposition.RadonNikodym and the Avram, Palmowski and Pistorius (2007) scale-function dividend argument

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.sigmaFinite_absolutelyContinuous_has_real_density (μ : Measure ℝ) [SigmaFinite μ] (hμac : μ ≪ (volume : Measure ℝ)) : ∃ K : ℝ → ℝ, Measurable K ∧ (∀ x : ℝ, 0 ≤ K x) ∧ μ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) := by sorry
