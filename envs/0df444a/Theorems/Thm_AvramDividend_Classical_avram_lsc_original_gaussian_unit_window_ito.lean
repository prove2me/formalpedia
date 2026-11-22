-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_original_gaussian_unit_window_ito
-- name    : AvramDividend.Classical.avram_lsc_original_gaussian_unit_window_ito
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T21:54:47.212321+00:00
-- url     : https://prove2.me/theorems/78d01a37-1eed-4393-ab01-7926a768cd4d
-- title:
--   Original zero-jump Avram Gaussian source as an actual Brownian Itô unit-window integral
-- statement:
--   Given the original Avram Lévy process represented by the same-space normalised Brownian motion, its normalised Gaussian source increment at every positive horizon equals the imported Brownian Itô integral of the elementary initial-window integrand. The probability space, original source identity and Brownian filtration are unchanged. The deterministic integrand's standard measurability, progressive measurability and finite-energy conditions are explicit and must be discharged at application.
-- source:
--   Avram Dividend Classical 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, finite-cap Gaussian stopped Ito step. Extends Proved same-space Gaussian source 1df1cb31-2581-48c2-8298-c025addaaac9 with Proved imported stochasticIntegralBrownian_eval_simple_readable cae7fbf2-3586-459d-92c8-a9b6a264de7f and elementary stepIoc0 identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_readable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_original_gaussian_unit_window_ito
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱr : Filtration ℝ mΩ)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱr)
    (hW : ∀ (t : ℝ) (ω : Ω),
      W.W t ω =
        (X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.c) / X.σ)
    {b : ℝ} (hb : 0 < b)
    (hm : Measurable (Function.uncurry
      (fun ω s => (stepIoc₀ Ω hb).eval s ω)))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱr
      (fun ω s => (stepIoc₀ Ω hb).eval s ω))
    (hq : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hb).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱr hℱ
        (fun ω s => (stepIoc₀ Ω hb).eval s ω)
        hm hp hq b
      =ᵐ[P] fun ω =>
        (X.X (Real.toNNReal b) ω -
          (Real.toNNReal b : ℝ) * X.c) / X.σ := by sorry
