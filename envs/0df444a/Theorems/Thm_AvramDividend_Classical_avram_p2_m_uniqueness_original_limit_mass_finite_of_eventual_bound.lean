-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_limit_mass_finite_of_eventual_bound
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_limit_mass_finite_of_eventual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:56:11.445059+00:00
-- url     : https://prove2.me/theorems/22d589f0-5038-46b6-87d4-f7be40d72f5c
-- title:
--   Original mass-limit finiteness from eventual mass bound
-- statement:
--   If the original real-measure total masses converge to the total mass of a proposed image limit, and their total masses are eventually bounded by a finite extended nonnegative constant, then the limiting image has finite total mass. P2-B's original X.X moment limit at k=0 and its proved uniform mass bound supply the exact hypotheses, establishing finiteness of the genuine weighted X.ν image without independent integrability assumptions.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_limit_mass_finite_of_eventual_bound
    {ι : Type*} (l : Filter ι) [NeBot l]
    (μi : ι → Measure ℝ) (η : Measure ℝ) (C : ℝ≥0∞)
    (hC : C < ⊤)
    (hmass : ∀ᶠ i in l, (μi i) Set.univ ≤ C)
    (hlim : Tendsto (fun i => (μi i) Set.univ) l (nhds (η Set.univ))) :
    η Set.univ < ⊤ := by sorry
