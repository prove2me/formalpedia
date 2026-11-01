-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_strictly_decreasing_tilt
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_decreasing_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:44:27.050669+00:00
-- url     : https://prove2.me/theorems/4b912ea6-b6b6-421e-bec2-f8876b8e4697
-- title:
--   Strict decrease in admissible real Esscher tilt of the original killed first-record spatial resolvent
-- statement:
--   For the actual original first-record time T_h and reflected drawdown D_a, no Standing, and divergent first small-negative-jump absolute moment, the height resolvent R_a(θ)=∫_{h>0}exp(-θh)E_P[exp(-qT_h);T_h<D_a] dh is strictly decreasing in θ on the full admissible interval θ>−φ. The Proved exact original spatial moment formula R_a(θ)=1/(θ+W′(a)/W(a)) and the Proved lower hazard bound W′/W≥φ ensure both denominators positive, so the strict reciprocal order law applies. This theorem is about a spatial weight of the original process, not an Esscher-changed process or an excursion intensity.
-- source:
--   Canonical genuine first-record spatial exponential moment resolvent cefb902e, source hazard bound, pinned one_div_lt_one_div.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_decreasing_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    StrictAntiOn (fun θ : ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) (Ioi (-φ)) := by sorry
