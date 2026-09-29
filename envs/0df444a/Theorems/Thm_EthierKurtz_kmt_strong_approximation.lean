-- Prove2me | Theorems.Thm_EthierKurtz_kmt_strong_approximation
-- name    : EthierKurtz.kmt_strong_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:00:31.160652+00:00
-- url     : https://prove2.me/theorems/0f9eda2d-0bf5-4e41-aac0-891ba2f48a17
-- title:
--   Theorem 5.1 — strong approximation of independent sums
-- statement:
--   Let μ be a probability distribution on the real line whose exponential moments are finite throughout some neighborhood of zero. Then one can construct, on one probability space, an iid sequence with law μ and a Brownian motion having the same mean and variance per unit time, together with positive constants C, K, and λ depending only on μ, such that for every integer n at least one and every positive x, the probability that the maximum discrepancy between the first n partial sums and the Brownian motion at the corresponding integer times exceeds C log n + x is strictly less than K exp(-λx). No centering or positive-variance assumption is imposed.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986 (held reprint 1986/2005), Chapter 7, Section 5, Theorem 5.1, equation (5.1), printed p. 356 (PDF p. 365).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

/-- KMT coupling with the source's strict exponential tail and logarithmic error.
The coordinate ξ i denotes source ξ_{i+1}; no nondegeneracy is assumed. -/
theorem kmt_strong_approximation
    (μ : ProbabilityMeasure ℝ)
    (hexp : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ)) :
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
