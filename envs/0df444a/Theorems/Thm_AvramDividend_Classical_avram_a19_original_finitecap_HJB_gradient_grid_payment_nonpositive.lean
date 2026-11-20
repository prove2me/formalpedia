-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
-- name    : AvramDividend.Classical.avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:08:45.750398+00:00
-- url     : https://prove2.me/theorems/67be5e16-c7d6-4097-9272-2ac2fc146b0b
-- title:
--   Original finitecap HJB gradient implies full physical grid payment sign
-- statement:
--   Full finite physical right dividend grid with original HJB derivative at least one below cap. The discounted cap-linear payment residual is nonpositive, including prepayment overshoots beyond cap. The proof combines endpoint continuity and interior derivative secant bound with exact scalar caplinear cell inequalities.
-- source:
--   Physical finite right dividend grid sign using original HJB gradient.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
    {ι : Type*} (s : Finset ι) (w : ℝ → ℝ) (C : ℝ)
    (Y D E : ι → ℝ)
    (hYlo : ∀ i ∈ s, 0 ≤ Y i)
    (hYhi : ∀ i ∈ s, Y i ≤ C)
    (hD : ∀ i ∈ s, 0 ≤ D i)
    (hE : ∀ i ∈ s, 0 ≤ E i)
    (hcont : ContinuousOn w (Ici 0))
    (hdiff : ∀ i ∈ s, DifferentiableOn ℝ w (Ioo (Y i) C))
    (hgrad : ∀ i ∈ s, ∀ t ∈ Ioo (Y i) C, 1 ≤ deriv w t) :
    (∑ i ∈ s, E i * (D i + w (Y i) -
      (if Y i + D i ≤ C then w (Y i + D i)
       else w C + (Y i + D i - C)))) ≤ 0 := by sorry
