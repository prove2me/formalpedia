-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_from_envelope
-- name    : AvramDividend.Classical.causal_neumann_C1_resolvent_from_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:05:06.89591+00:00
-- url     : https://prove2.me/theorems/e09e39f9-5203-478d-9e54-264198af343d
-- title:
--   C1 Gaussian Neumann resolvent from dominated signed convolution powers
-- statement:
--   A causal signed L1 convolution-power sequence dominated by contracting positive powers with geometric mass and quadratic pointwise control has an explicitly represented resolvent series continuous at zero and continuously differentiable for positive time. It packages the entire analytic C1 regularity part of the Gaussian Esscher scale-function argument.
-- source:
--   Use the accepted signed-power continuity theorem and the envelope pointwise bound for hP. Define scaled exponential primitives H_n. Apply accepted continuity and mass-bound lemmas, treating x=0 by the empty Ioc integral. The accepted signed-primitive Neumann C1 criterion constructs g. This is directly instantiated by the Gaussian damped kernel and its contracting positive envelope in the open Esscher derivative-resolvent target.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_signed_power_continuity_from_envelope
import Theorems.Thm_AvramDividend_Classical_causal_exp_scaled_primitive_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_of_signed_primitives

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_C1_resolvent_from_envelope
    (k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hP0 : P 0 = k)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by sorry
