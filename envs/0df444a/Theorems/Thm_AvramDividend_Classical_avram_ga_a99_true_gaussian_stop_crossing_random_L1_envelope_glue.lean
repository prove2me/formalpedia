-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a99_true_gaussian_stop_crossing_random_L1_envelope_glue
-- name    : AvramDividend.Classical.avram_ga_a99_true_gaussian_stop_crossing_random_L1_envelope_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:13:35.43655+00:00
-- url     : https://prove2.me/theorems/4d8283fb-c1f2-42f7-92ff-fe17c9820c4e
-- title:
--   Original stopped Gaussian at-most-one crossing cell positive L1 vanishes from one random terminal envelope
-- statement:
--   For each original stopped Gaussian mesh, a single crossing cell with positive error bounded by a common nonnegative integrable random envelope has expected positive error tending to zero whenever the envelope does. The bound has no factor of the number of mesh cells.
-- source:
--   Original Avram Gaussian positive interior one-sided L1 physical full/cross/post partition, building on the proved single-cell crossing budget lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a99_true_gaussian_stop_crossing_random_L1_envelope_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Ω → Finset ℕ) (f : ℕ → ℕ → Ω → ℝ)
    (B : ℕ → Ω → ℝ)
    (hCard : ∀ m ω, (S m ω).card ≤ 1)
    (hBn : ∀ m ω, 0 ≤ B m ω)
    (hBI : ∀ m, Integrable (B m) P)
    (hFI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m ω, max (f m i ω) 0) P)
    (hCell : ∀ m ω i, i ∈ S m ω → max (f m i ω) 0 ≤ B m ω)
    (hBLim : Tendsto (fun m => ∫ ω, B m ω ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, (∑ i ∈ S m ω, max (f m i ω) 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
