-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_local_neumann_convolution_majorant
-- name    : AvramDividend.Classical.causal_local_neumann_convolution_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:10:39.847232+00:00
-- url     : https://prove2.me/theorems/04015f37-51d8-4fb0-b515-3c2b54f2b03b
-- title:
--   Locally bounded Neumann sums admit the required causal convolution majorant
-- statement:
--   Local uniform bounds on finite Gaussian Neumann sums imply the dominated-convergence convolution majorant on each positive horizon. This permits exponential growth of the Gaussian resolvent outside that horizon, unlike a global uniform bound.
-- source:
--   The Gaussian undamped Neumann sums can grow exponentially as time increases. Use a bound on each finite horizon Ioc(0,x), rather than a globally uniform bound. The common integrable majorant D(s)=C‖B(x-s)‖ suffices almost everywhere under volume.restrict, using ae_restrict_mem measurableSet_Ioc. This supplies exactly hDom of causal_neumann_resolvent_dominated_convergence.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Basic

open MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_local_neumann_convolution_majorant
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hB : ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume)
    (hQ : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖(∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ C) :
    ∀ x : ℝ, ∃ D : ℝ → ℝ,
      IntegrableOn D (Ioc (0 : ℝ) x) volume ∧
      (∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ D s) := by sorry
