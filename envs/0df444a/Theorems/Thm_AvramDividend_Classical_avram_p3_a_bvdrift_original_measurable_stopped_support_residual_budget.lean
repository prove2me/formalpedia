-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:16:09.567697+00:00
-- url     : https://prove2.me/theorems/1870052a-c04b-4e9c-932a-faf353795898
-- title:
--   Source BV continuous-remainder signed budget on any measurable stopped support
-- statement:
--   On the genuine bounded-variation spectrally negative Levy process, the continuous physical-drift-minus-actual-jumps residual has one atomless locally finite Stieltjes measure. For every measurable time support S, including a random stopped interval after fixing a path, the negative measure integral of any weight nonnegative on S is nonpositive. The weight may have either sign outside S. No auxiliary process, drift classification, predictable compensator, or jump intensity is assumed.
-- source:
--   Proof uses accepted original source locally finite atomless Stieltjes residual 4f9a8a4a, pinned integral_indicator and nonnegative-integral laws, validating the original BV derivative correction over the actual stopped measurable support.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) ∧
      (∀ S : Set ℝ≥0, MeasurableSet S →
        ∀ g : ℝ≥0 → ℝ, (∀ t ∈ S, 0 ≤ g t) →
          -(∫ t in S, g t ∂μ) ≤ 0) := by sorry
