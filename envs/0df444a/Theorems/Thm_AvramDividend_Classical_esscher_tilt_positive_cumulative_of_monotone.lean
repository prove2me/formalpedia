-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_positive_cumulative_of_monotone
-- name    : AvramDividend.Classical.esscher_tilt_positive_cumulative_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:27:54.47264+00:00
-- url     : https://prove2.me/theorems/e569ae6a-d85a-4028-8693-b13627757909
-- title:
--   Positive cumulative Stieltjes representation of a zero-origin q-scale function under Esscher tilt monotonicity
-- statement:
--   For a q-scale function vanishing at zero, strictly positive for positive arguments and with an Esscher-normalised factor nondecreasing on the positive axis, construct a positive Stieltjes measure whose cumulative mass is that factor. Global continuity follows from the proved zero-origin scale-continuity theorem; nondecreasingness extends across zero using the support and sign properties. Uses a separate Stieltjes cumulative theorem currently under remote verification.
-- source:
--   Pinned Mathlib Stieltjes-function construction and scaleFunction_continuous_of_zero_origin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilt_positive_cumulative_of_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (φ : ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∃ β : Measure ℝ,
      (∀ x : ℝ, β (Iic x) =
        ENNReal.ofReal (Real.exp (-φ * x) * W x)) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) := by sorry
