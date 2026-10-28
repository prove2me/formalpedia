-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_integral_telescope
-- name    : AvramDividend.Classical.causal_neumann_finite_integral_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:00:04.687046+00:00
-- url     : https://prove2.me/theorems/ece5103e-a3eb-4b8b-9950-1ee5084192dd
-- title:
--   Finite Neumann resolvent identity for the actual causal Volterra integral operator
-- statement:
--   Let T be the causal Volterra convolution operator with kernel B and scalar coefficient 1/a. If Q_0=F and Q_(n+1)=-TQ_n, and all kernel products are integrable on the relevant (0,x] intervals, then the finite Neumann partial sum S_n satisfies S_n+TS_n=F-Q_(n+1) as a function equality. This specialises the previously accepted abstract algebraic telescope to the concrete integral operator needed for the Gaussian scale-function regularity proof.
-- source:
--   Combine Proved finite telescoping and finite integral-sum exchange with exact integrability hypotheses.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_resolvent_telescope
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_finset_sum

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_finite_integral_telescope
    (a : ℝ) (B F : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q i) +
      (fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i s) ∂volume)) =
      F - Q (n + 1) := by sorry
