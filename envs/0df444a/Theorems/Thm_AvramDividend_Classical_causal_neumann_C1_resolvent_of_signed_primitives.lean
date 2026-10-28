-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_of_signed_primitives
-- name    : AvramDividend.Classical.causal_neumann_C1_resolvent_of_signed_primitives
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:59:01.010017+00:00
-- url     : https://prove2.me/theorems/ba9fde8f-9929-4293-8753-8464fc53b0c3
-- title:
--   Complete Neumann resolvent C1 from signed L1 power and primitive data
-- statement:
--   Given Gaussian signed convolution powers with quadratic-geometric bounds and continuous scaled primitives of geometrically decaying size, positive-time L1 continuity of each power suffices to construct a continuous-on-nonnegative C1-on-positive complete Neumann resolvent. Reduces the remaining analytic work for the Gaussian Esscher target to verifying envelope bounds and the resolvent integral equation.
-- source:
--   Instantiate the accepted signed-power L1 derivative-transfer theorem at each power P_n to discharge the exact HasDerivAt hypotheses of the Proved complete Neumann resolvent theorem. Positive-time power continuity and nonnegative-time primitive continuity supply the derivative-expression continuity on compact positive intervals.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_derivative_from_positive_L1
import Theorems.Thm_AvramDividend_Classical_causal_neumann_full_resolvent_regular_of_correction_bounds

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_C1_resolvent_of_signed_primitives
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hPbound : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hHbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHdef : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P n s ∂volume)) / a)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPcont : ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ))) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a +
        Real.exp (w * y) * (∑' n : ℕ, H n y)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by sorry
