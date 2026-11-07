-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
-- name    : AvramDividend.Classical.avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:11:54.143096+00:00
-- url     : https://prove2.me/theorems/9258c362-b30a-4a13-83a2-0d9acd039a7a
-- title:
--   Original infinite-cap gaussian HJB supersolution growth envelope
-- statement:
--   For the exact unbounded-variation Lévy gaussian regime, show that the source C² HJB supersolution has some global nonnegative exponential upper-growth envelope.
-- source:
--   Source-exact original analytic growth certificate. Together with the existing bounded stopped clock, nonnegative terminal payoff and proved exponential-growth L1 theorem, this reduces the corresponding infinite-cap integrability case.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hCtop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by sorry
