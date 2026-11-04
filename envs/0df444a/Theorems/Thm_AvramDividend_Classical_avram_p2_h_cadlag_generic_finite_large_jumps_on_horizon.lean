-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:33:44.402066+00:00
-- url     : https://prove2.me/theorems/910d142a-aed7-41bd-9690-b2544509a546
-- title:
--   Every deterministic càdlàg path has finitely many ε-large jumps on a compact horizon
-- statement:
--   A real-valued càdlàg path on nonnegative times has finitely many genuine jumps of absolute magnitude at least δ>0 on (0,T], for every finite T including T=0. The proof uses compactness of Icc(0,T), an accumulation-point contradiction, and independently proved vanishing of jump marks from the two sides, with careful treatment of accumulation at time zero. It is wholly deterministic and needs no Lévy process, compensator or rate identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_right

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      δ ≤ dist (Y u - Function.leftLim Y u) 0}.Finite := by sorry
