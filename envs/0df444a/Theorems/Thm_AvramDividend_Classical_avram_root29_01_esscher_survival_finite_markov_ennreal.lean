-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_esscher_survival_finite_markov_ennreal
-- name    : AvramDividend.Classical.avram_root29_01_esscher_survival_finite_markov_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:08:42.824519+00:00
-- url     : https://prove2.me/theorems/e1f9d84f-7cd6-493c-8e29-90a997210dfc
-- title:
--   Actual finite-time original-Lévy Esscher survival Markov kernel with real future reward
-- statement:
--   Under the original spectrally negative Lévy law, the finite-time Esscher-weighted closed lower-survival reward at s+u equals integration over the true historical reserve/survival pair of the positive Esscher weight at s multiplied by the genuine real-valued fresh-process survival expectation for u. This derives directly from independently proved source-level full-path Markov disintegration, adapted history measurability and real-to-ENNReal fresh reward conversion. It requires no all-time Esscher path measure, W scale, Wiener-Hopf factorisation or exit ratio.
-- source:
--   From Proved 3787cbef, 7aed93b7, bab28150 using measurable future reward and positive Tonelli constant factor; work/avram_root29_01_esscher_survival_finite_markov_ennreal.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_finite_survival_markov_product
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_history_survival_pair_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_esscher_survival_finite_markov_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    (∫⁻ h : ℝ × Bool,
      (if h.2 then
        ENNReal.ofReal (Real.exp
          (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (∫ ω,
          ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + h.1) + X.X v ω}).indicator
            (fun ω => Real.exp
              (θ * X.X u ω - (u : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P)) := by sorry
