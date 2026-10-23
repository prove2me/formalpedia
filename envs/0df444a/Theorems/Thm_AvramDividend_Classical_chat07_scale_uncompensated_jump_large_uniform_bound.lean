-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_uncompensated_jump_large_uniform_bound
-- name    : AvramDividend.Classical.chat07_scale_uncompensated_jump_large_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:13:34.416807+00:00
-- url     : https://prove2.me/theorems/4f069279-de8b-4ef9-ae16-f44b7cb55028
-- title:
--   Uniform weighted scale difference bound for large negative jumps
-- statement:
--   For a nonnegative Laplace parameter in the scale-function domain and any downward jump magnitude at least one, the weighted integral of the absolute scale displacement is bounded by the reciprocal scale Laplace denominator. This is independent of jump size and pairs with finite large-jump Lévy measure mass to give the large-jump Fubini majorant.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_uncompensated_jump_large_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 1 ≤ r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) * |W x - W (x-r)|) ≤
      (X.ψ θ - q)⁻¹ := by sorry
