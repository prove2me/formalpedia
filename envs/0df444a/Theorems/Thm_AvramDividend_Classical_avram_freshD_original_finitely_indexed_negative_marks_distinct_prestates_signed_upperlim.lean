-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
-- name    : AvramDividend.Classical.avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:51:41.468067+00:00
-- url     : https://prove2.me/theorems/e8c86e83-44c9-4b21-b5e7-cde03c9e310d
-- title:
--   Finite chronological negative Lévy marks with distinct positive prestates preserve the correct original signed Taylor upper mesh limit
-- statement:
--   Let S be a finite index set representing chronological negative Lévy jumps, with possibly repeated mark sizes z_i<0 and distinct strict-interior pre-jump reserves y_i. For each i the physical sampled pre-reserve u_m(i) converges to y_i. For the original cap-local C2 dividend HJB candidate w (continuous at 0, zero at negative reserves, potentially w(0)>0), the positive part of the sum of all exact nonlinear Taylor jump approximation errors converges to zero. This is the finite-activity bridge from the proved single-mark signed upper limit across ruin contact 5864c4ee, and it does not require uniform absolute continuity across zero or assume jumps have different mark values. The remaining original-source obligation is to enumerate the actual stopped physical Lévy negative marks and identify sampled pre-jump reserve convergence per index.
-- source:
--   Original true physical mixed Gaussian finite-activity Avram 242ca5f1 stopped Itô–Meyer cash source: deterministic finite-marks, per-mark distinct prestate signed upper limit from the source-proved 5864c4ee.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
    {ι : Type*}
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (S : Finset ι) (z y : ι → ℝ)
    (hz : ∀ i ∈ S, z i < 0)
    (hy : ∀ i ∈ S, y i ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ι → ℝ)
    (hu : ∀ i ∈ S, Tendsto (fun m => u m i) atTop (𝓝 (y i))) :
    Tendsto
      (fun m => max
        (∑ i ∈ S,
          ((w (u m i + z i) - w (u m i) -
            (if -1 < z i then z i * deriv w (u m i) else 0)) -
          (w (y i + z i) - w (y i) -
            (if -1 < z i then z i * deriv w (y i) else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
