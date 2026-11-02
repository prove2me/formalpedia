-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_chronological_levy_then_dividend_generator_bound
-- name    : AvramDividend.Classical.avram_wave5_03_actual_discounted_chronological_levy_then_dividend_generator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:32:51.695236+00:00
-- url     : https://prove2.me/theorems/683c1730-f310-45fb-8da6-d98b22e7f81d
-- title:
--   Discounted original negative Lévy jump followed by admissible right dividend is dominated by exact generator mark correction
-- statement:
--   For one original spectrally negative Levy sample, capped admissible adapted left-continuous dividends, a strictly pre-ruin positive time t≤T and actual negative source jump mark J, assume its original strict pre-source reserve Y lies in the indicated interior mark band. Then e^{-qt} times the full chronological nonlinear reserve increment from before the Levy jump to after the right dividend, plus that actual right dividend atom, is at most e^{-qt} times the source small-mark linear term Jw'(Y)1_{J>-1} plus the exact generatorIntegrand w Y J. This uses the same source path X and D and same t and 𝓕, the Proved 03B literal prepayment source jump identity/kernel, and our Proved separate-gradient all-cap right atom inequality. No stochastic compensation, Gaussian driver or independence assumption. Handles positive pre-ruin times; the time-zero atom is separately Proved, and a positive ruin-time right dividend is deliberately excluded.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), source Lévy jump followed chronologically by right dividend and HJB control term in stopped (5.13). Integrator bridge to canonical BV ef7e6c20 and corrected UBV 429e17ca. Nonduplicate synthesis of 03B Proved 509cd0f3 and e336f7e2 with integrator 2cd50555, on identical original X,D,t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_discounted_chronological_levy_then_dividend_generator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (htRuin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u v ζ : ℝ) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w (x + X.X t ω - rightLimit D t ω) -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) +
        (rightLimit D t ω - D t ω)) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by sorry
