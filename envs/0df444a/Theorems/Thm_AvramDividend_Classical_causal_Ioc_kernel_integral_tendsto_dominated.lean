-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_tendsto_dominated
-- name    : AvramDividend.Classical.causal_Ioc_kernel_integral_tendsto_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:25:44.570018+00:00
-- url     : https://prove2.me/theorems/6b8746e0-c040-43aa-bc63-8dd5854d50cd
-- title:
--   Dominated convergence for a finite causal Volterra convolution integral
-- statement:
--   Let f_n converge almost everywhere to g under the restricted Lebesgue measure on (0,x]. If each reflected-kernel product B(x-s)f_n(s) is strongly measurable and dominated by one integrable function D(s), then their causal integral converges to the integral of B(x-s)g(s). This supplies the limit-interchange hypothesis needed in the infinite Neumann Volterra resolvent identity.
-- source:
--   The Bochner integral dominated-convergence theorem for the restricted measure on (0,x], applying pointwise convergence after multiplication by the reflected kernel.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_Ioc_kernel_integral_tendsto_dominated
    (B : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g D : ℝ → ℝ) (x : ℝ)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * f n s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hD : IntegrableOn D (Ioc (0 : ℝ) x) volume)
    (hbound : ∀ n : ℕ,
      ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * f n s‖ ≤ D s)
    (hpoint : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
      Tendsto (fun n : ℕ => f n s) atTop (nhds (g s))) :
    Tendsto (fun n : ℕ =>
      ∫ s in Ioc (0 : ℝ) x, B (x - s) * f n s ∂volume)
      atTop (nhds
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume)) := by sorry
