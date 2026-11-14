-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:22:12.089532+00:00
-- url     : https://prove2.me/theorems/cf315c0c-f642-491c-8b94-dcf1098d8b24
-- title:
--   Original finite-cap full negative-mark increment admits small-jump Lipschitz and large-jump bounded envelope
-- statement:
--   At a finite dividend cap c, for pre-reserves y bounded away from zero, a locally Lipschitz candidate on the interior upper band, bounded on the nonnegative reserve interval and zero on negative reserves has full unmasked jump increment controlled by L times claim size for marks smaller than epsilon over two, and by twice the candidate bound for all larger negative marks. This rigorously retains nonzero w(0) and allows a genuine BV Levy first moment and finite tail intensity to furnish an integrable dominating function needed for source cap jump DCT.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
    (w : ℝ → ℝ) (c ε L M : ℝ)
    (hε : 0 < ε) (hεc : ε ≤ c)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hBound : ∀ r ∈ Icc (0 : ℝ) c, |w r| ≤ M)
    (hLip : ∀ a ∈ Icc (ε / 2) c, ∀ b ∈ Icc (ε / 2) c,
      |w a - w b| ≤ L * |a - b|)
    (y z : ℝ) (hy : y ∈ Icc ε c) (hz : z < 0) :
    ‖w (y + z) - w y‖ ≤
      ‖if -(ε / 2) ≤ z then L * |z| else 2 * M‖ := by sorry
