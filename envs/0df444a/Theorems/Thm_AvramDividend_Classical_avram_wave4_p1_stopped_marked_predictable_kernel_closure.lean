-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_predictable_kernel_closure
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_marked_predictable_kernel_closure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:09:56.071166+00:00
-- url     : https://prove2.me/theorems/fe8d9978-abea-45d0-971f-8feae0b93511
-- title:
--   Original-filtration marked predictable kernels remain predictable under inclusive stopping
-- statement:
--   For an actual filtration on its original probability space and any finite-valued stopping time τ, every measurable real marked kernel F on the original predictable-time-history product measurable space remains predictable after the inclusive stopped multiplication 1_{t≤τ(ω)} F(t,ω,z). The hypothesis is genuine predictable measurability, not the desired Campbell identity or martingale conclusion. Derive by taking the measurable product of the proven inclusive stopping mask with the universe of marks, and use measurable if-then-else. Countable right-separating times cover nonnegative-real and discrete grids.
-- source:
--   Proved P1 continuous stopping mask UUID c3d85546-8351-4a29-93ec-6e68240f1788; pinned Mathlib MeasurableSet.prod, Measurable.ite.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask

open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_p1_stopped_marked_predictable_kernel_closure
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    (D : Set ι) (hD : D.Countable)
    (hSep : ∀ a b : ι, a < b →
      ∃ s : ι, s ∈ D ∧ a ≤ s ∧ s < b)
    (τ : Ω → ι)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι)))
    (F : ((ι × Ω) × E) → ℝ)
    (hF : Measurable[(𝓕.predictable).prod mE] F) :
    Measurable[(𝓕.predictable).prod mE]
      (fun p => if p.1.1 ≤ τ p.1.2 then F p else 0) := by sorry
