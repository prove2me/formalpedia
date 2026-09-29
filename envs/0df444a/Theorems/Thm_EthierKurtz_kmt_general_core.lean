-- Prove2me | Theorems.Thm_EthierKurtz_kmt_general_core
-- name    : EthierKurtz.kmt_general_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T20:00:00.631015+00:00
-- url     : https://prove2.me/theorems/ebe29135-e5ab-4cfc-8a70-4c96c619a58f
-- title:
--   KMT strong approximation with general centering and scale
-- statement:
--   For a real probability law with a finite exponential moment around the origin, there is a coupling of an iid sequence with a Brownian motion whose partial sums differ from the Brownian motion with the law mean drift and standard deviation scaling by at most logarithmic order, with an exponential tail bound.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356, before specializing to mean zero and variance one.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

theorem kmt_general_core
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real))
 :
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
