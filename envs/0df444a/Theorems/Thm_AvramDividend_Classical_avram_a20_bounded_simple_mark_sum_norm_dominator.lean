-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_simple_mark_sum_norm_dominator
-- name    : AvramDividend.Classical.avram_a20_bounded_simple_mark_sum_norm_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T20:57:22.677504+00:00
-- url     : https://prove2.me/theorems/6acad207-8d40-4201-8d51-f2951863e40f
-- title:
--   Unit-bounded finite weighted centred original marked-count sum dominated by raw count plus compensator
-- statement:
--   For finite real arrays of jump-cell counts N_i≥0 and deterministic compensation rates r_i≥0, and mark weights satisfying |a_i|≤1, the absolute value of the centred finite weighted sum ∑a_i(N_i−r_i) is at most ∑(N_i+r_i). By applying the triangle inequality to the finite sum, then |a_i||N_i−r_i|≤|N_i−r_i|≤N_i+r_i, this yields a pointwise uniform dominating random variable for all finite-valued original Borel jump-mark approximants. Under the Proved original finite-activity count-square integrability it supplies the required common square-integrable bound for passing to the exact original bounded-mark compensated L2 isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_bounded_simple_mark_sum_norm_dominator
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (a N r : ι → ℝ)
    (ha : ∀ i ∈ F, |a i| ≤ 1)
    (hN : ∀ i ∈ F, 0 ≤ N i)
    (hr : ∀ i ∈ F, 0 ≤ r i) :
    |∑ i ∈ F, a i * (N i - r i)| ≤
      ∑ i ∈ F, (N i + r i) := by sorry
