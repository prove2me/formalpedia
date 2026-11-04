-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_prepayment_original_cutoff_residual_nonpos
-- name    : AvramDividend.Classical.avram_p4_c_generator_prepayment_original_cutoff_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:47:27.161928+00:00
-- url     : https://prove2.me/theorems/397a8bb2-6252-4cb6-8754-9d80751e10c6
-- title:
--   Genuine controlled prepayment reserve has nonpositive original epsilon-physical generator residual from strict interior HJB
-- statement:
--   At an actual adapted left-limit controlled reserve Y(t,omega)=leftLim(x+X.X-rightLimit D), whenever 0<Y and ENNReal.ofReal Y<C, the full original drift/Gaussian/negative-jump epsilon-cutoff expression with b_epsilon=c−∫_{-1<z<-epsilon}zν and raw jumps on z<=-1 and -1<z<-epsilon, plus the small compensated remainder, is at most q*w(Y). The original HJB GeneratorIntegrable and generator inequality suffice. This proves the exact one-sided generator sign at genuine interior stopped reserves, without claiming process measurability, Ito martingales or boundary values.
-- source:
--   Proved full original epsilon drift identification helper and source X.generator, original controlled prepayment reserve and HJB assumptions; paper Proposition 4(i) and Equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_prepayment_original_cutoff_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (0 < Y ∧ ENNReal.ofReal Y < C) →
      X.σ ^ 2 / 2 * iteratedDeriv 2 w Y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w Y +
        (∫ z in Iic (-1 : ℝ), w (Y + z) - w Y ∂X.ν) +
        (∫ z in Ioo (-1 : ℝ) (-ε), w (Y + z) - w Y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) -
        q * w Y ≤ 0 := by sorry
