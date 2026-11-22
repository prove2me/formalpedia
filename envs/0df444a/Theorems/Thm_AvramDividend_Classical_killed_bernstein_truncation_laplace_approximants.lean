-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_truncation_laplace_approximants
-- name    : AvramDividend.Classical.killed_bernstein_truncation_laplace_approximants
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:38:34.655506+00:00
-- url     : https://prove2.me/theorems/fa660c84-f7f0-460b-8391-1b6d4b24a414
-- title:
--   Finite-truncation killed-geometric potentials with uniform Laplace lower bounds and convergence
-- statement:
--   Given a σ-finite positive-half-line Lévy kernel κ with finite compensated Laplace integrals and a positive killing k, construct a continuous-at-zero Bernstein denominator F and a SEQUENCE of finite measures βₙ from truncated finite-jump killed geometric potentials. They all have mass 1/k, positive support and Laplace transforms lower-bounding 1/F(s), and their Laplace transforms converge to 1/F(s) for s≥0. In particular 1/F(s) equals the full inverse killed Bernstein exponent. The theorem isolates the genuine jump-truncation/convergence difficulty so the already-Proved tightness and weak-limit theorems close the finite potential existence goal 5422d653.
-- source:
--   Proved killed-geometric potential 9f7bf7a2, original compensated tail identity 0cb20c38, Mathlib monotone convergence; feeds Proved f2895e24 tightness and 32aa3f05 Laplace weak limit. Child of 5422d653.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_truncation_laplace_approximants
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤) :
    ∃ (F : ℝ → ℝ) (β : ℕ → Measure ℝ),
      F 0 = k ∧ ContinuousAt F 0 ∧
      (∀ s : ℝ, 0 ≤ s → 0 < F s) ∧
      (∀ n : ℕ, β n Set.univ = ENNReal.ofReal (k⁻¹)) ∧
      (∀ n : ℕ, β n (Iio (0 : ℝ)) = 0) ∧
      (∀ n : ℕ, ∀ s : ℝ, 0 < s →
        ENNReal.ofReal ((F s)⁻¹) ≤
        (∫⁻ x : ℝ,
          ENNReal.ofReal (Real.exp (-(s * x))) ∂β n)) ∧
      (∀ s : ℝ, 0 ≤ s →
        Tendsto
          (fun n : ℕ =>
            ∫⁻ x : ℝ,
              ENNReal.ofReal (Real.exp (-(s * x))) ∂β n)
          atTop (𝓝 (ENNReal.ofReal ((F s)⁻¹)))) ∧
      (∀ s : ℝ, 0 < s →
        ENNReal.ofReal ((F s)⁻¹) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by sorry
