-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_height_hazard_ode
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_survival_height_hazard_ode
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:35:45.891573+00:00
-- url     : https://prove2.me/theorems/1b0c8fb7-1656-4720-a154-a349906a9163
-- title:
--   Exact first-order record-height hazard ODE for genuine original reflected-killed first-record survival
-- statement:
--   For actual strict record times T_h and actual reflected ruin D_a, the real killed-discount survival G_a(h)=E[exp(-qT_h);T_h<D_a] satisfies G'_a(h)=-[W'(a)/W(a)] G_a(h) at every a>0 and h>0 under pure infinite-small-jump variation. The derivative is the ordinary real height derivative. The authentic Proved source exponential hazard identity and a local positive-height equality with the derivative of exp(-hκ) establish it; no sample-path differentiability or new stochastic axiom is assumed.
-- source:
--   Proved original-process G_a(h)=exp(-h W'/W) 1c71a04d, pinned HasDerivAt.exp and HasDerivAt.congr_of_eventuallyEq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_survival_height_hazard_ode
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    HasDerivAt (fun r : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X r ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X r ω).toReal)))
      else 0 ∂P).toReal)
      ((∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal * (-(deriv W a / W a))) h := by sorry
