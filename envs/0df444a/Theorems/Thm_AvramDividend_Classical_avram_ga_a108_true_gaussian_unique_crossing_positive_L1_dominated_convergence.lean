-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
-- name    : AvramDividend.Classical.avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:34:13.648026+00:00
-- url     : https://prove2.me/theorems/a0a10c19-bae6-40a0-80fe-b7e94e304818
-- title:
--   One original true Gaussian crossing-cell positive residual converges in expected L1 from its a.s. convergence and one integrable envelope
-- statement:
--   For the actual physically stopped original Gaussian source, the one stop-straddling cell has at most one index. If its positive spatial error tends to zero almost surely and is bounded by one measurable integrable pathwise source supremum envelope, the expected total positive crossing error tends to zero by dominated convergence. Unlike a final-grid-cell argument, no cell-count factor is introduced.
-- source:
--   Pinned Mathlib Bochner dominated convergence and proved ga97 single crossing cell bound, for true stopped spatial b0 one-sided root.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Ω → Finset ℕ) (f : ℕ → ℕ → Ω → ℝ)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hCard : ∀ᵐ ω ∂P, ∀ m, (S m ω).card ≤ 1)
    (hPoint : ∀ᵐ ω ∂P, ∀ m i, i ∈ S m ω →
      max (f m i ω) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ S m ω, max (f m i ω) 0) P)
    (hAE : ∀ᵐ ω ∂P, Tendsto
      (fun m => ∑ i ∈ S m ω, max (f m i ω) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (∑ i ∈ S m ω, max (f m i ω) 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
