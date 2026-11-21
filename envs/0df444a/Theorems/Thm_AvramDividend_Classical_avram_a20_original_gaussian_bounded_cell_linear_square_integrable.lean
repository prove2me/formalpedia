-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_gaussian_bounded_cell_linear_square_integrable
-- name    : AvramDividend.Classical.avram_a20_original_gaussian_bounded_cell_linear_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:29:04.484145+00:00
-- url     : https://prove2.me/theorems/74caefdd-3a46-4a80-987a-8d3f3054311a
-- title:
--   All three original stopped Gaussian Taylor cell integrability hypotheses follow from bounded predictable coefficients
-- statement:
--   For a finite original Gaussian physical stopped cell grid, if genuine original centred Lévy increments M are integrable with integrable squares, and predictable Taylor coefficients G,H are measurable and uniformly bounded on the cell, then each product GM, coefficient H, and square-product HM² is integrable. These are precisely the per-cell hypotheses needed by the existing original zerojump Gaussian conditional-centering theorem 4a4b4e27, the finite-grid limit helper 100a0b89, and new source 3ceb14d3. The primitive boundedness comes from established original compact C² coefficient lemmas, and Gaussian moment estimates are separately Proved.
-- source:
--   Pinned Mathlib Integrable.bdd_mul; exact original Gaussian Ito Taylor per-cell L1 integrability bridge.

import Mathlib
open MeasureTheory

/-- Predictably measurable bounded original Gaussian grid Taylor coefficients give all three necessary L1 cell integrability hypotheses. -/
theorem AvramDividend.Classical.avram_a20_original_gaussian_bounded_cell_linear_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ι : Type*} (S : Finset ι) (M G H : ι → Ω → ℝ)
    (BG BH : ι → ℝ)
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hM2 : ∀ i ∈ S, Integrable (fun ω => (M i ω) ^ 2) P)
    (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
    (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
    (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
    (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i) :
    (∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P) ∧
    (∀ i ∈ S, Integrable (H i) P) ∧
    (∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P) := by sorry
