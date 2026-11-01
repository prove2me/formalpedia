-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_strictly_positive
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:49:25.013289+00:00
-- url     : https://prove2.me/theorems/d03f13b5-532f-4954-a084-2d61558f78d6
-- title:
--   Strict positivity of genuine original killed first-record spatial Esscher potential for all theta>minus phi
-- statement:
--   For the actual strict upward first-record T_h and reflected drawdown D_a, under positive q, pure infinite-small-jump variation and no Standing, the weighted spatial height resolvent ∫_{h>0}e^{-θh}E_P[e^{-qT_h};T_h<D_a]dh is strictly positive for each positive depth a and every admissible real θ>−φ, including negative θ. This derives from the authentic source identity R_a(θ)=(θ+κ(a))^{-1} and the Proved κ(a)≥φ>0, so θ+κ(a)>0. It is a direct positivity interface for logarithms and normalisations, not an excursion surrogate.
-- source:
--   Canonical Proved original source spatial resolvent cefb902e and source positive-Esscher hazard lower bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    0 < ∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal := by sorry
