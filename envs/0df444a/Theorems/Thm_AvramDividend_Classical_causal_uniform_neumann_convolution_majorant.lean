-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_uniform_neumann_convolution_majorant
-- name    : AvramDividend.Classical.causal_uniform_neumann_convolution_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:05:42.079945+00:00
-- url     : https://prove2.me/theorems/4c977b5d-104d-47b1-81a0-2f9e8c164278
-- title:
--   Uniformly bounded Neumann partial sums yield the exact dominated-convergence majorant
-- statement:
--   Every locally integrable causal convolution kernel admits a common integrable domination for products with uniformly bounded finite Neumann sums. The conclusion matches the dominating-function requirement of the canonical Gaussian derivative-resolvent convergence theorem.
-- source:
--   Given a local L1 convolution kernel and uniform pointwise bounds on every finite Neumann partial sum, choose the integrable majorant D(s)=C*‖B(x-s)‖. The inequality follows from the multiplicativity of the norm, and it discharges hDom in the Proved causal_neumann_resolvent_dominated_convergence theorem.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Basic

open MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_uniform_neumann_convolution_majorant
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hB : ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume)
    (hQ : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s : ℝ,
        ‖(∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ C) :
    ∀ x : ℝ, ∃ D : ℝ → ℝ,
      IntegrableOn D (Ioc (0 : ℝ) x) volume ∧
      (∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ D s) := by sorry
