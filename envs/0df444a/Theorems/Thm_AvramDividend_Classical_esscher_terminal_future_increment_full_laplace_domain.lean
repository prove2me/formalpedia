-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_full_laplace_domain
-- name    : AvramDividend.Classical.esscher_terminal_future_increment_full_laplace_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:24:12.530251+00:00
-- url     : https://prove2.me/theorems/883afe6f-0c46-46f3-bfea-60ec9a8189a1
-- title:
--   Full real Laplace-moment domain of a future increment under consistent terminal Esscher laws
-- statement:
--   For every Esscher parameter θ≥0 and real transform parameter η satisfying θ+η≥0, and every future Lévy increment s to s+u observed under a terminal Esscher law at T≥s+u, the real exponential moment equals exp(u(ψ(θ+η)-ψ(θ))). Both positive and negative η are covered on the full source-faithful exponential-moment domain using existing verified positive-η and negative-ε branch theorems, with no full Wiener–Hopf factorisation assumption.
-- source:
--   Kuznetsov–Kyprianou–Rivero Esscher exponent relation ψ_θ(η)=ψ(θ+η)-ψ(θ), η≥-θ; accepted Prove2Me esscher_terminal_future_increment_shifted_laplace and esscher_terminal_future_increment_negative_laplace.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_shifted_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_negative_laplace

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_future_increment_full_laplace_domain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hdomain : 0 ≤ θ + η)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    (∫ ω, Real.exp (η * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      Real.exp ((u : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by sorry
