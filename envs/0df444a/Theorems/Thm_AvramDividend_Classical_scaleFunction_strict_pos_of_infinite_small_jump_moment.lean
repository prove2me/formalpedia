-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_infinite_small_jump_moment
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_infinite_small_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:02:33.977867+00:00
-- url     : https://prove2.me/theorems/3521b36a-f1c4-4e87-b930-447f2a621fdc
-- title:
--   A canonical q-scale function is strictly positive when the small-jump first moment is infinite
-- statement:
--   If the canonical spectrally negative Lévy process has infinite first absolute moment of its small negative jumps, then every q-scale function value W(a) is strictly positive for a>0. The proof is analytic: the infinite moment forces ψ eventually above q, the universal Lévy estimate bounds ψ quadratically, and the scale-function Laplace identity rules out an initial zero interval.
-- source:
--   Compose Proved psi_eventually_gt_of_infinite_small_jump_moment, the generic eventual-positive quadratic packaging, and Proved scaleFunction_strict_pos_of_eventual_psi_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_strict_pos_of_infinite_small_jump_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ a : ℝ, 0 < a → 0 < W a := by sorry
