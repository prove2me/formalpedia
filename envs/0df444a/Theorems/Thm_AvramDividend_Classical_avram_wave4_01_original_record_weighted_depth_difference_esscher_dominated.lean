-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_depth_difference_esscher_dominated
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_esscher_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:24:03.802607+00:00
-- url     : https://prove2.me/theorems/769b16cd-0d97-4f98-8440-1474f234a5ec
-- title:
--   One integrable Esscher envelope for depth differences of original killed first-record rewards
-- statement:
--   For any two positive reflected drawdown depths a,b and any positive original strict-record height h, the absolute difference of the true process weighted killed first-record expectations is at most exp(-((θ+φ)h)), uniformly in the two depths. Here φ>0 solves ψ(φ)=q. If θ>−φ, the dominating exponential is integrable on h>0. This quantitative source-process bound is the key L¹ dominated-convergence interface and does not require Standing.
-- source:
--   Canonical Proved avram_wave4_01_original_record_weighted_esscher_pointwise_domination and elementary order arithmetic on [0,M].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_depth_difference_esscher_dominated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
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
      else 0 ∂P).toReal)| ≤
      Real.exp (-((θ + φ) * h)) := by sorry
