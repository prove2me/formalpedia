-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_weight_integrable
-- name    : AvramDividend.Classical.avram_root29_01_history_survival_weight_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:32:01.81499+00:00
-- url     : https://prove2.me/theorems/a4195aa0-d468-4681-869a-7de51929c89d
-- title:
--   Original Lévy historical Esscher survival reward dominated-integrable at random reserve
-- statement:
--   For any genuine source spectrally negative Lévy process, nonnegative Esscher parameter, historical deterministic horizon s and future horizon u, the closed-history-survival indicator of the original Esscher density at s times the true real original-P future nonruin Esscher expectation evaluated at the random reserve x+X_s is Bochner integrable under the original P. The future mass lies in [0,1] and is monotone in reserve, so the measurable historical reward is dominated by the canonical integrable Esscher density. No scale or stopped first-passage theorem is assumed.
-- source:
--   WS1A source work/avram_root29_01_history_survival_weight_integrable.lean; Proved 701eb6a8, 28aaafa3, f07a704e, cf6d2ea5.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_root29_01_history_survival_weight_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0) :
    Integrable
      (fun ω : Ω =>
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω) P := by sorry
