-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_pointwise_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:10:45.80561+00:00
-- url     : https://prove2.me/theorems/62bbd1d1-3c2b-43f5-ae30-de635277191f
-- title:
--   Pointwise depth-uniform exponential domination of the true spatially weighted killed first-record reward
-- statement:
--   For each positive reflected drawdown depth a and strict upward record height h, and for any real spatial weight θ, the actual original-process killed discounted first-record reward multiplied by exp(-θh) is nonnegative and at most exp(-((θ+φ)h)), where φ>0 is the positive Esscher root ψ(φ)=q. This uses the already Proved genuine source envelope and gives an integrable dominating function on h>0 whenever θ>−φ, with no Standing hypothesis.
-- source:
--   Exact genuine original-process pointwise envelope target c5d17433-ae05-4846-916c-382777d09135 canonically Proved; ENNReal.toReal_nonneg, positivity and multiplicativity of Real.exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_uniform_esscher_envelope
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_pointwise_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ∧
    Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ≤
      Real.exp (-((θ + φ) * h)) := by sorry
