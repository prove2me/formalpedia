-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
-- name    : AvramDividend.Classical.chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:36:14.217569+00:00
-- url     : https://prove2.me/theorems/36c95a18-480f-4dfa-bf67-3fa059fc753e
-- title:
--   Zero-start killed q-scale harmonicity from almost-sure downward crossing before the horizon
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, if almost every path goes below zero at some time not later than the horizon, then its survival-killed discounted q-scale payoff from initial reserve zero vanishes almost everywhere. The scale-function value W(0) is zero under unbounded variation. Hence the killed renewal identity holds at zero starting capital, conditional on the explicit downcrossing property.
-- source:
--   Boundary x=0 of the Open chat04_unbounded_killed_survival_discounted_scale_expectation (a885f0b3-3960-424d-97e4-abbcffe268ba), in the proof chain of chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34-200b-4736-a369-5ae8473e3258). Imports Proved chat04_scale_zero_origin_of_unbounded_variation (c1b8958a-41fd-444e-893e-cf03e591b93e). The open downstream issue is to derive almost-sure early downcrossing from unbounded variation, or establish killed q-harmonicity directly for x>0.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (t : ℝ≥0)
    (hdown : ∀ᵐ ω ∂P, ∃ s : ℝ≥0, s ≤ t ∧ X.X s ω < 0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W 0) := by sorry
