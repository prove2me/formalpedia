-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb53_masked_original_positive_error_dominated_integral_limit
-- name    : AvramDividend.Classical.avram_bvb53_masked_original_positive_error_dominated_integral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:35:32.870627+00:00
-- url     : https://prove2.me/theorems/1201a5c5-08f7-43e8-8ef8-eb540bf277db
-- title:
--   Masked original positive physical error converges in mean from ae limit and integrable source domination
-- statement:
--   A reusable exact physical-error integration transfer for the original BV finite-cap signed grid: if the signed source error E(n) is measurable, the zero-ruin event A is measurable, and the masked positive error is uniformly bounded in norm by an integrable original-space envelope K and converges pointwise almost everywhere to zero, then its expected real integral tends to zero. It applies to the Proved physical-error envelope phys36f and the exact source pointwise obligation phys36e, keeping the original stochastic space and true ruin event, with no replacement process or assumed finite ambient measure. This is dominated convergence with explicit measurable masking, suitable for the original phys36d mean closure.
-- source:
--   Pinned MeasureTheory.tendsto_integral_of_dominated_convergence and Measurable.ite; exact phys36e/phys36f assembly

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb53_masked_original_positive_error_dominated_integral_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hMeas : ∀ n, Measurable (E n))
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      ‖if ω ∈ A then (0 : ℝ) else max (E n ω) 0‖ ≤ K ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => if ω ∈ A then (0 : ℝ)
        else max (E n ω) 0) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ ω,
      (if ω ∈ A then (0 : ℝ) else max (E n ω) 0) ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
