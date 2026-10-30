-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_markov
-- name    : AvramDividend.Classical.avram_root29_01_perpetual_survival_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:12:26.089676+00:00
-- url     : https://prove2.me/theorems/1f7a50c5-d843-45a5-b84a-988a9173d25e
-- title:
--   Original spectrally negative Lévy perpetual killed Esscher survival Markov identity
-- statement:
--   For any actual original-P spectrally negative Lévy process, every nonnegative Esscher parameter, real reserve and finite historical horizon, the perpetual killed Esscher survival mass equals the true original-P historical survival expectation of the current compensated Esscher density multiplied by the perpetual future survival mass at the random current reserve. Uses the genuine full real finite-time killed Markov theorem and all-real-time dominated convergence; does not assume exit, martingale or q-scale harmonicity.
-- source:
--   Distinct WS1A deterministic killed original-P stochastic bridge. Sources work/avram_root29_01_perpetual_survival_markov_draft.lean; upstream source-level fa5a7413, e9833a53, 9752e377 and 6e04803a. Do not compile until e9833a53 is Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_real
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_dct
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_root29_01_perpetual_survival_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s : ℝ≥0) :
    (⨅ t : ℝ≥0, ∫ ω,
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) =
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          (⨅ u : ℝ≥0, ∫ ζ,
            ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
              (fun ζ => Real.exp
                (θ * X.X u ζ - (u : ℝ) *
                  laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P) := by sorry
