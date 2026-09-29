-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_transfer
-- name    : EthierKurtz.kmt_affine_transfer
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T18:24:13.181788+00:00
-- url     : https://prove2.me/theorems/d2269163-c0e5-4c11-9e15-0f3c81b63e5e
-- title:
--   Affine transfer for KMT strong approximation
-- statement:
--   Show that the centered, unit-variance KMT coupling theorem implies the same strong approximation for every real probability law with an exponential moment near zero, including the zero-variance case. This transfer handles centering, scaling, and degenerate laws.
-- source:
--   Reduction step for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1, equation (5.1), p. 356.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

theorem kmt_affine_transfer
    (H : ∀ (ν : ProbabilityMeasure Real),
      (Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
        Integrable (fun x : Real => Real.exp (a * x)) (ν : Measure Real)) ->
      MeasureTheory.integral (ν : Measure Real) (fun x : Real => x) = 0 ->
      variance (fun x : Real => x) (ν : Measure Real) = 1 ->
        ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
      iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (ν : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
      IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        let m := ∫ x : ℝ, x ∂(ν : Measure ℝ)
        let σ := Real.sqrt (variance (fun x : ℝ => x) (ν : Measure ℝ))
        let W := fun (t : ℝ≥0) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
          m * (t : ℝ) + σ * z.2.val t
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)))
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
      ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
      iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (μ : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
      IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        let m := ∫ x : ℝ, x ∂(μ : Measure ℝ)
        let σ := Real.sqrt (variance (fun x : ℝ => x) (μ : Measure ℝ))
        let W := fun (t : ℝ≥0) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
          m * (t : ℝ) + σ * z.2.val t
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by sorry

end EthierKurtz
