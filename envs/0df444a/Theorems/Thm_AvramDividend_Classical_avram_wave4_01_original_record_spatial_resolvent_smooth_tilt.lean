-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_smooth_tilt
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_smooth_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:37:32.33254+00:00
-- url     : https://prove2.me/theorems/308df7ac-18ef-44dd-99f6-9f4865f3a51d
-- title:
--   C-infinity smoothness in the entire admissible Esscher tilt range of the genuine original first-record spatial resolvent
-- statement:
--   For the true original spectrally negative Lévy process under positive discount and divergent first absolute small-negative-jump moment, the spatial first-record killed-reward potential θ↦∫_0∞exp(-θh)E[e^{-qT_h};T_h<D_a] dh is infinitely differentiable for every θ>−φ, including negative θ, where φ>0 solves ψ(φ)=q. The exact Proved original-process resolvent equals (θ+W′(a)/W(a))^{-1}; the positive Esscher-root lower bound ensures its denominator never vanishes on this whole interval. No Standing, tilted/excursion clock, or analytic axiom is used.
-- source:
--   Genuine original-process spatial exponential moment resolvent cefb902e, genuine source hazard lower bound, and pinned Mathlib ContDiffOn.div.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_smooth_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ ⊤ (fun θ : ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) (Ioi (-φ)) := by sorry
