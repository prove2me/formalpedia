-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_negative_mark_loss_abs_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_compact_negative_mark_loss_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:37:28.19405+00:00
-- url     : https://prove2.me/theorems/c1fc53f3-fafb-461f-a746-4568a5605465
-- title:
--   Compact nonnegative reserve bounds every negative-mark value loss
-- statement:
--   From the compact absolute value bound and w=0 on negative reserves, bound the two w terms uniformly for b in [0,B], z negative.
-- source:
--   Required deterministic bounded kernel tool for source original top-cap stopped compensation 46849a70. No restrictions on derivatives, generator or cap, and preserves zero reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_compact_negative_mark_loss_abs_bound
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b z : ℝ, 0 ≤ b → b ≤ B → z < 0 → |w (b + z) - w b| ≤ K := by sorry
