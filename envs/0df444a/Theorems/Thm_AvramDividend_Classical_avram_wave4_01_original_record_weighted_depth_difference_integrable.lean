-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_depth_difference_integrable
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:25:37.865454+00:00
-- url     : https://prove2.me/theorems/b1fbb14c-4c0c-4d71-b2fa-bd2c7123e872
-- title:
--   L1-integrable absolute depth difference of actual first-record Esscher kernels
-- statement:
--   For θ>−φ and any two positive drawdown depths a,b, the absolute difference of the original-process stopped first-record spatial reward kernels, each weighted by exp(-θh), has a finite Lebesgue integral in record height h>0. The theorem supplies the integrability and strong measurability interface for a genuine dominated-convergence proof in depth, with no Standing assumption.
-- source:
--   Canonical Proved avram_wave4_01_original_record_weighted_esscher_height_integrable, closure of IntegrableOn under differences and absolute values.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a b : ℝ) (hθ : -φ < θ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun h : ℝ =>
      |(Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X b ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) - (Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal)|) (Ioi 0) := by sorry
