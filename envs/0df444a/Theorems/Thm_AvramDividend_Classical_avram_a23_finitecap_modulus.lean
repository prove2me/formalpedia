-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_finitecap_modulus
-- name    : AvramDividend.Classical.avram_a23_finitecap_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:39:22.873331+00:00
-- url     : https://prove2.me/theorems/0af6907a-202d-44d9-85bb-94a1eb103a30
-- title:
--   Finitecap HJB reserve modulus
-- statement:
--   Uniform continuity gives a spatial modulus on the compact capped reserve interval.
-- source:
--   Compact original HJB reserve modulus.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a23_finitecap_modulus
    (w : ℝ → ℝ) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y z : ℝ,
      0 ≤ y → y ≤ b → 0 ≤ z → z ≤ b →
      |y - z| < δ → |w y - w z| < ε := by sorry
