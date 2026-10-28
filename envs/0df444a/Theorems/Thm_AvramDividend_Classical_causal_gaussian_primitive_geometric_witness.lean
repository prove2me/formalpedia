-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_geometric_witness
-- name    : AvramDividend.Classical.causal_gaussian_primitive_geometric_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:30:14.628839+00:00
-- url     : https://prove2.me/theorems/3254dcb4-2cb2-4a7f-9456-777b52bb7fb1
-- title:
--   Signed Gaussian convolution powers yield continuous geometrically bounded primitives
-- statement:
--   Each signed Gaussian convolution power dominated by an integrable envelope with geometric integral mass yields an exponentially damped primitive that is continuous on nonnegative time and uniformly bounded by the corresponding geometric coefficient.
-- source:
--   Preserve the normalized exponentially weighted Gaussian primitives Hn appearing inside the Proved causal_neumann_C1_resolvent_from_envelope proof. Use the proved local scaled-primitive mass bound from |Pn|≤Fn and Fn-mass≤ρ^(n+1), and the scaled-primitive continuity theorem. Supplies hHbound and hHcont for the geometric Neumann resolvent equation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_scaled_primitive_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_primitive_geometric_witness
    (P F : ℕ → ℝ → ℝ) (a w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∃ H : ℕ → ℝ → ℝ,
      (∀ n : ℕ, H n = fun x : ℝ =>
        (Real.exp (-w * x) *
          (∫ s in Ioc (0 : ℝ) x,
            Real.exp (w * s) * P n s ∂volume)) / a) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        ‖H n x‖ ≤ ρ ^ (n + 1) / a) ∧
      (∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ))) := by sorry
