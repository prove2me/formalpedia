-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_renormalised_resolvent_laplace
-- name    : AvramDividend.Classical.causal_renormalised_resolvent_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:56:01.663887+00:00
-- url     : https://prove2.me/theorems/e107cad8-3ef7-4fcf-979b-8d66d1638f0e
-- title:
--   Exact q-scale Laplace mass from the tilted Neumann convolution series
-- statement:
--   For a nonnegative causal renewal sequence whose tilted kernel has transform q/ψ with 0<q<ψ, the renormalised series W(x)=exp(θx)ΣFn(x)/q has Laplace integral exactly 1/(ψ-q). First use the proved geometric convolution-power series Laplace identity at η-θ, then move the exponential tilt and scalar outside the integral and simplify the geometric fraction. Provides the numerical Laplace clause of positive-discount scale construction; integrability of W must still be proved separately.
-- source:
--   Proved causal_convolution_power_series_exact_laplace and the real exponential addition law.

import Theorems.Thm_AvramDividend_Classical_causal_convolution_power_series_exact_laplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_renormalised_resolvent_laplace
    (K : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ η q ψ : ℝ)
    (hq : 0 < q) (hψ : q < ψ)
    (hKi : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * K x)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = K)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        K s * F n (x - s) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hKmass : (∫ x in Ioi (0 : ℝ),
      Real.exp (-((η - θ) * x)) * K x ∂volume) = q / ψ) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(η * x)) *
        ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)) ∂volume) =
      1 / (ψ - q) := by sorry
