-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_discounted_c1_strict_interior_stopped_residual_budget
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_discounted_c1_strict_interior_stopped_residual_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:53:00.985684+00:00
-- url     : https://prove2.me/theorems/98ae208b-f074-4dd4-97f7-5f40e2d83765
-- title:
--   Original bounded-variation residual: discounted C1 derivative on strict-interior stopped support
-- statement:
--   For the actual original spectrally negative Levy process on its unchanged sample space, probability and filtration, BV yields an atomless locally finite Stieltjes measure for physical-drift-minus-source-path-minus-actual-negative-jumps. For any random stopped measurable time support and controlled reserve known to lie strictly between 0 and cap, the same main HJB gradient lower bound 1 <= deriv w gives a nonpositive discounted negative contribution from that continuous residual. No drift classification, vanishing residual, auxiliary Poisson model, or compensation law is assumed.
-- source:
--   Source proof specialises previously Proved avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget to the actual stopped support and weight exp(-q*t) * deriv w(U t), uses exp positivity and the strict-interior gradient hypothesis.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_discounted_c1_strict_interior_stopped_residual_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (U : ℝ≥0 → Ω → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (S : Ω → Set ℝ≥0) (hS : ∀ ω, MeasurableSet (S ω))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hInterior : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      0 < U t ω ∧ ENNReal.ofReal (U t ω) < C) :
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
      -(∫ t in S ω,
        Real.exp (-q * (t : ℝ)) * deriv w (U t ω) ∂μ) ≤ 0 := by sorry
