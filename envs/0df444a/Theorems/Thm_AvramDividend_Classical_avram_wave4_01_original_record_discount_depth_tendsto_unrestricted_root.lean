-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:24:23.708014+00:00
-- url     : https://prove2.me/theorems/80304468-d3a4-4d91-a3de-a0b777e0405f
-- title:
--   Actual reflected first-record discount converges to unrestricted upcrossing discount as drawdown tolerance tends to infinity
-- statement:
--   For every fixed positive first-record height h, the genuine spectrally negative Lévy expectation E[e^{-qT_h};T_h<D_a] tends to exp(-h φ(q)) as the actual permitted reflected drawdown a tends to infinity, for infinite-small-negative-jump variation without Standing. The limit is the Proved unrestricted strict-upcrossing Laplace transform. The proof combines the genuine source exponential record-height law with the previously isolated source hazard asymptotic K(a)→φ.
-- source:
--   Original source semigroup exponent 1f5b13d3 and source hazard asymptotic parent d455bcb7. No excursion substitution; genuine original first-upcrossing T_h and real reflected ruin D_a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h) :
    Tendsto
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      atTop (nhds (Real.exp (-(h * φ)))) := by sorry
