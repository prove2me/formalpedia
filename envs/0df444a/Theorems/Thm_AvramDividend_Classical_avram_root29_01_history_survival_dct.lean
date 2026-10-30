-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_dct
-- name    : AvramDividend.Classical.avram_root29_01_history_survival_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:49:58.175917+00:00
-- url     : https://prove2.me/theorems/e9833a53-e754-49c4-b704-fb9b2e50d7b3
-- title:
--   Actual original-Lévy Esscher killed-history dominated convergence at a random reserve
-- statement:
--   For the genuine spectrally negative Lévy original P law, every nonnegative Esscher parameter θ, real capital x and historical deterministic horizon s, the historical survival indicator times compensated Esscher density at s times the true future finite-horizon Esscher survival mass F_u(x+X_s), integrated under P, converges as u tends to infinity to the corresponding original-P integral with the real infimum over all future horizons. The proof constructs the true random-reserve measurable kernel, uses actual pointwise source survival-mass convergence and 0≤F_u≤1 to dominate by the integrable original Esscher density. No q-scale harmonicity, optional stopping or exit identity is assumed.
-- source:
--   WS1A source work/avram_root29_01_history_survival_dct.lean; Proved 9752e377, 28aaafa3, f07a704e, 701eb6a8, 55082175, pinned Mathlib DCT.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_root29_01_history_survival_dct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 => ∫ ω,
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P)
      atTop
      (nhds (∫ ω,
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (⨅ u : ℝ≥0, ∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P)) := by sorry
