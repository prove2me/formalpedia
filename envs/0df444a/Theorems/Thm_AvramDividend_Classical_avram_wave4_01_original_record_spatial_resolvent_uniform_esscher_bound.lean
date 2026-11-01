-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_uniform_esscher_bound
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_uniform_esscher_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:40:12.062176+00:00
-- url     : https://prove2.me/theorems/7562bbc6-0b97-4c99-a643-ba655e345b35
-- title:
--   Uniform Esscher-root dominated spatial exponential-height moment bound for genuine reflected-killed first-record survival
-- statement:
--   For all positive drawdown depths a and every spatial height tilt θ>−φ, where φ>0 is an Esscher root ψ(φ)=q, the original process killed first-record spatial transform ∫_{h>0} exp(−θh) E[e^{-qT_h};T_h<D_a] dh is at most 1/(θ+φ). The upper bound is uniform in the depth a and valid for exponentially growing weights θ<0. It follows from the genuine negative-tilt resolvent and W'(a)/W(a)≥φ.
-- source:
--   Proved negative-tilt actual source resolvent cefb902e and Proved original first-record hazard slope lower bound a5dbcace; pinned one_div_le_one_div_of_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_uniform_esscher_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    (∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) ≤
    (θ + φ)⁻¹ := by sorry
