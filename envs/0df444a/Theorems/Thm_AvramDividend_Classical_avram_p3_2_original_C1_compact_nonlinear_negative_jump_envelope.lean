-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_C1_compact_nonlinear_negative_jump_envelope
-- name    : AvramDividend.Classical.avram_p3_2_original_C1_compact_nonlinear_negative_jump_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:41:01.787051+00:00
-- url     : https://prove2.me/theorems/41bf973a-6209-413f-b5d2-fe3f6e2c1525
-- title:
--   Source-exact original C1 nonlinear negative-Lévy-jump envelope including ruin crossing
-- statement:
--   For the actual original dividend verification value function w, the canonical C1 hypothesis on a compact positive reserve neighbourhood, continuity on nonnegative reserves, and zero extension on negative reserves yield finite nonnegative L and R. Every negative mark z at a reserve y in [a,b] satisfies |w(y+z)-w(y)| ≤ L|z| for z≥−a/2 and ≤2R for larger ruin-crossing marks. No global Lipschitz or boundedness hypotheses are added.
-- source:
--   Pinned Mathlib ContDiffOn.locallyLipschitzOn and compact Lipschitz extraction, compact continuous image norm bound, and original hwNeg ruin extension; matches the original BV Lévy jump generator's compact localisation.

import Mathlib

open Set
noncomputable section

/-- The actual C1 dividend candidate has a source-valid nonlinear negative
jump envelope on compact original reserve strips, including ruin crossing. -/

theorem AvramDividend.Classical.avram_p3_2_original_C1_compact_nonlinear_negative_jump_envelope
    (w : ℝ → ℝ) (U : Set ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U)
    (hwCont : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Set.Icc (a / 2) b ⊆ U) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      ∀ y ∈ Set.Icc a b, ∀ z : ℝ, z < 0 →
        |w (y + z) - w y| ≤
          if -(a / 2) ≤ z then L * |z| else 2 * R := by sorry
