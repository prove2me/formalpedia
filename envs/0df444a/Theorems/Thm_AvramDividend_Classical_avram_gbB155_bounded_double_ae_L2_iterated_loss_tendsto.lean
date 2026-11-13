-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
-- name    : AvramDividend.Classical.avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:23:30.356207+00:00
-- url     : https://prove2.me/theorems/ee53d690-9e27-4419-898d-43852dbe9579
-- title:
--   Bounded double almost-everywhere convergence implies iterated L2 loss tends to zero
-- statement:
--   Proved B136 gives iterated L2 convergence from product almost-everywhere convergence. The pinned Mathlib ae_ae_comm and ae_prod_iff_ae_ae theorems convert the reversed iterated almost-everywhere statement into product almost-everywhere, provided the pointwise convergence event is measurable.
-- source:
--   Proved B136 and pinned Mathlib measure product lemmas

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α × β → ℝ) (g : α × β → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m z, |f m z| ≤ B) (hgb : ∀ z, |g z| ≤ B)
    (hMeas : MeasurableSet {z : α × β |
      Tendsto (fun m : ℕ => f m z) atTop (𝓝 (g z))})
    (hae : ∀ᵐ b ∂ν, ∀ᵐ a ∂μ,
      Tendsto (fun m : ℕ => f m (a,b)) atTop (𝓝 (g (a,b)))) :
    Tendsto (fun m : ℕ =>
      ∫ a, (∫ b, (f m (a,b) - g (a,b)) ^ 2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
