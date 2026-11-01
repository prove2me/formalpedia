-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_residual_continuousAt_cap_of_unbounded_variation
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousAt_cap_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:19:37.71573+00:00
-- url     : https://prove2.me/theorems/7487a881-2157-4dc5-b94f-35d996503f28
-- title:
--   Full residual continuity at positive optimal cap for every unbounded-variation Lévy source under original smoothness
-- statement:
--   For the actual source X under Standing, a genuine q-scale W at q>0 with finite positive optimal cstar, and the original three-way barrier smoothness hypothesis, if X is of unbounded variation, the actual compensated Lévy generator residual of vcstar is continuous at exactly cstar. This includes both Gaussian and non-Gaussian unbounded variation, strictly strengthening the previously Proved pure-jump global C2 residual continuity interface. The Proved global smooth-fit theorem supplies ContDiffOn 2 vcstar on Ioi0, the true scale origin is zero by Gaussian or infinite small jumps, and the proved monotone nonnegative continuous value function satisfies the already Proved weighted compact generator-continuity theorem, using a locally uniform y^2 majorant. No interior harmonicity or above-barrier inequality is assumed.
-- source:
--   Avram, Palmowski, Pistorius (2007) positive cstar endpoint generator domain and smooth fit; Kuznetsov, Kyprianou, Rivero (2013), generator and C2 Gaussian scale regularity; P3 actual source compact dominated-convergence theorem d574f843.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousAt_cap_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hnbv : ¬ X.BoundedVariation)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousAt
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (cstar W).toReal := by sorry
