-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_tendsto_zero_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:11:38.284275+00:00
-- url     : https://prove2.me/theorems/e877e7b4-16d8-4b74-8ec2-11fffd3d5fdb
-- title:
--   Genuine killed strict-record discount vanishes as positive reflected drawdown allowance shrinks to zero
-- statement:
--   For any fixed positive strict upward record height h, the actual original Lévy stopped discount G_a(h)=E[exp(-qT_h); T_h<D_a] tends to zero when the allowed reflected drawdown depth a decreases to zero through positive values, assuming divergent negative small-jump first moment. The Proved genuine semigroup exponential law gives G_a(h)=exp(-h K(a)) and the source near-zero hazard divergence gives K(a)→+infinity. Real exponential decay then yields the desired original-process first-record extinction. No Standing or excursion surrogate.
-- source:
--   Genuine original record exponential hazard 1f5b13d3-98f1-4b35-b1d2-5df29b3cf596 and pending source hazard boundary 800cd189-f02c-439e-8919-17259775ab86.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (h : ℝ) (hh : 0 < h) :
    Tendsto
      (fun a : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) := by sorry
