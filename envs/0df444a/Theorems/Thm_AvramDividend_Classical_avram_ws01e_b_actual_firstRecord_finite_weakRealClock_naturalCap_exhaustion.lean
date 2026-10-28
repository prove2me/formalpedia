-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:59:59.076675+00:00
-- url     : https://prove2.me/theorems/ef0377ba-2f27-4e88-b050-087c003014dd
-- title:
--   Exact actual first-record finite-age and weak real-clock natural-cap exhaustion
-- statement:
--   For the genuine first strict upper record of the spectrally negative Lévy path, the finite-record event equals the increasing union of natural finite cap events, and the same union identity holds with the *real* observation-clock weak inequality T_b.toNNReal<=t. This source-specific event statement is the exact cap-exhaustion step required to remove the deterministic record cap from the accepted true random-terminal Esscher full-future-path reward factor. It preserves the weak real-clock cutoff of the capped proof; it assumes no probability, Markov, WH or scalar factor identity.
-- source:
--   For any ENNReal T<top, the coercion (T.toNNReal:ENNReal)=T; choose a natural bound from exists_nat_gt T.toNNReal. Conversely each T<n implies T<top. Intersect the finite-age event with the unchanged real-clock weak inequality to derive the joint path-clock union. This theorem is a structural child of the E150-refused direct uncapped Qp regeneration proof f5788ba0, not a generic new DCT helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    ({ω : Ω | twoSidedExitUpTime X b ω < ⊤} =
      ⋃ n : ℕ, {ω : Ω |
        twoSidedExitUpTime X b ω < (n : ℝ≥0∞)}) ∧
    ({z : Ω × ℝ |
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2} =
      ⋃ n : ℕ, {z : Ω × ℝ |
        twoSidedExitUpTime X b z.1 < (n : ℝ≥0∞) ∧
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2}) := by sorry
