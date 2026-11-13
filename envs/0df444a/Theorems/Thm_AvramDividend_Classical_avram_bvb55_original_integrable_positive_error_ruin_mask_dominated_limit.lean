-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb55_original_integrable_positive_error_ruin_mask_dominated_limit
-- name    : AvramDividend.Classical.avram_bvb55_original_integrable_positive_error_ruin_mask_dominated_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:44:12.103783+00:00
-- url     : https://prove2.me/theorems/458f4258-8e40-4a33-b8d8-243d16a2a60a
-- title:
--   Original masked integrable positive physical error converges in mean under source domination
-- statement:
--   For the original signed physical-grid error, integrability of each positive part implies its almost-everywhere strong measurability. The zero-ruin mask A is measurable by the original-process stopping-time result; therefore the masked error is also almost-everywhere strongly measurable using the indicator of A complement. Given an integrable original-space envelope and almost-everywhere zero convergence, Bochner dominated convergence yields convergence of the expected masked error to zero. This removes the stronger global Measurable E requirement in the Proved bvb53 helper and is designed for the exact phys36c/phys36e/phys36f mean transfer.
-- source:
--   Pinned Mathlib Integrable.pos_part, AEStronglyMeasurable.indicator, tendsto_integral_of_dominated_convergence; source phys36f and bvb54.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb55_original_integrable_positive_error_ruin_mask_dominated_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) (0 : ℝ)) P)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, ‖if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0‖ ≤ K ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun n => if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ ω, (if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0) ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
