-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_original_gaussian_unit_window_complete
-- name    : AvramDividend.Classical.avram_lsc_original_gaussian_unit_window_complete
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:49:46.518444+00:00
-- url     : https://prove2.me/theorems/49e15a41-1cf0-4e35-9e2c-60e8a11b13ca
-- title:
--   Original Avram Gaussian driver as Brownian Itô integral with all finite-energy and measurability conditions discharged
-- statement:
--   For each positive deterministic horizon, the exact Avram normalized Gaussian source on its original sample space equals a LevyStochCalc Brownian Itô integral against the same Brownian motion and original filtered clock. Unlike the preliminary theorem, the statement supplies concrete joint-measurability, progressive-measurability and square-integrability witnesses for the elementary window integrand, built from standard simple predictable calculus and the finite-horizon bounded-integrand energy lemma.
-- source:
--   Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Uses Proved finite energy 43090805-dff6-4165-8036-39ab2cf2f286, Proved LevyStochCalc simple predictable bound 1cd600b6-5e8b-4337-a77d-6ea63c207357 and Proved Itô simple integral cae7fbf2-3586-459d-92c8-a9b6a264de7f. No Open theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_abs_eval_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_readable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_original_gaussian_unit_window_complete
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
    {b : ℝ} (hb : 0 < b) :
    ∃ (hm : Measurable (Function.uncurry
          (fun ω s => (stepIoc₀ Ω hb).eval s ω)))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱr
          (fun ω s => (stepIoc₀ Ω hb).eval s ω))
      (hq : ∀ T, 0 < T →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖(stepIoc₀ Ω hb).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱr hℱ
          (fun ω s => (stepIoc₀ Ω hb).eval s ω)
          hm hp hq b
        =ᵐ[P] fun ω =>
          (X.X (Real.toNNReal b) ω -
            (Real.toNNReal b : ℝ) * X.c) / X.σ := by sorry
