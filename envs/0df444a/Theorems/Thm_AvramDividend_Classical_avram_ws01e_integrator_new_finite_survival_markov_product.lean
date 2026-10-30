-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_finite_survival_markov_product
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_finite_survival_markov_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:18:13.85216+00:00
-- url     : https://prove2.me/theorems/3787cbef-9e0e-4dd9-a49c-5a77399c9bd8
-- title:
--   True finite-horizon Esscher lower-survival law factors through original Levy past endpoint and independent full shifted path
-- statement:
--   For the actual spectrally negative Levy process under its original probability P, any deterministic s,u and fixed Esscher parameter theta, the Esscher-weighted survival expectation through s+u equals the true iterated original-P law of the observed past endpoint/survival flag and the whole fresh future increment path. The historical endpoint/survival state is required to be measurable in F_s, an honest known source-Lévy condition. The future full-path nonruin event is exactly a rational-covering endpoint-containing schedule, not an artificial all-horizon tilted path-space probability. The accepted pathwise survival and exponential decompositions and the original-P full-path Markov-Tonelli source provide a noncircular proof, independently of Wiener-Hopf and positive-root differentiability.
-- source:
--   Source-faithful child supporting the deterministic killed q-scale semigroup needed downstream of accepted perpetual scalar 07c7d8b4 and all-real CDF 8c0f76fb. Accepted original-P full-future path Markov-Tonelli 77ced690, exact lower-survival split d829a33d, exact compensated Esscher exponential split 481efeaf, source shifted survival grid iff 67c7e86c, future path measurable set a484bed3. Does not claim killed stopped optional stopping or assume a product tilted path law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_lower_survival_future_increment_pathwise_split
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01e_integrator_new_finite_survival_markov_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u)
    (hH : Measurable[𝓕 s]
      (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω)))) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ∫⁻ h : ℝ × Bool, ∫⁻ y : ℝ≥0 → ℝ,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + h.1) + y (τ j) then
          ENNReal.ofReal (Real.exp
            (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
            Real.exp (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map (fun ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P) := by sorry
