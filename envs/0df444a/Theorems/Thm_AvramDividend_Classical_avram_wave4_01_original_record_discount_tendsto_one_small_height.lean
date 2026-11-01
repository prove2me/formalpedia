-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_tendsto_one_small_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_one_small_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:43:45.05166+00:00
-- url     : https://prove2.me/theorems/bdf59fc9-718f-4627-bd36-e5416ffded77
-- title:
--   Actual reflected first-record discount converges to one as positive record height shrinks to zero
-- statement:
--   For the original spectrally negative Levy process and genuine drawdown-ruin clock, fixed drawdown threshold a>0 and q>0, the discounted probability G_a(h) of reaching a strict positive upward record before reflected ruin approaches one as h decreases to zero through positive heights. Under divergent small negative jump variation, the Proved uncapped record-discount semigroup has exact G_a(h)=exp(-hK(a)) at positive h with finite K(a). Continuity of the real exponential at zero delivers the one-sided limit. This establishes the near-zero normalization of the actual stopped record kernel without Standing and without introducing a synthetic process or probability axiom.
-- source:
--   Genuine uncapped reflected-record exponential hazard 1f5b13d3-98f1-4b35-b1d2-5df29b3cf596 and real exponential continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_one_small_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 : ℝ)) := by sorry
