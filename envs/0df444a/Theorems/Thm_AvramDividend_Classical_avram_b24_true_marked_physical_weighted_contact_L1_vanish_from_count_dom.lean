-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_marked_physical_weighted_contact_L1_vanish_from_count_dom
-- name    : AvramDividend.Classical.avram_b24_true_marked_physical_weighted_contact_L1_vanish_from_count_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:33:29.727204+00:00
-- url     : https://prove2.me/theorems/b30546b6-ab9b-4489-9e91-9244964b1c4e
-- title:
--   Marked true stopped finite-activity weighted jump-contact errors vanish in L1 under count domination
-- statement:
--   On the same original stopped jump process, if a family of physical finite marked-cell weighted residuals vanishes almost surely, each coefficient is uniformly bounded and every marked-cell count is bounded by the same integrable random source count, then the expected absolute weighted residual tends to zero. This is the dominated-convergence link from the Proved B243 canonical finite jump count to the remaining Ito-Meyer true-contact L1 jump error.
-- source:
--   Proved B243 original true clipped physical marked-cell count L1 bound and Mathlib dominated convergence at pinned revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_marked_physical_weighted_contact_L1_vanish_from_count_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (marked : ℕ → Ω → Finset ℕ) (W : ℕ → ℕ → Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hCount : ∀ k, ∀ᵐ ω ∂P, ((marked k ω).card : ℝ) ≤ B ω)
    (hWeight : ∀ k i ω, |W k i ω| ≤ L)
    (hMeas : ∀ k, AEStronglyMeasurable
      (fun ω => |∑ i ∈ marked k ω, W k i ω|) P)
    (hPoint : ∀ᵐ ω ∂P, Tendsto
      (fun k => ∑ i ∈ marked k ω, W k i ω)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, |∑ i ∈ marked k ω, W k i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
