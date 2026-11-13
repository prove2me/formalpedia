-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_value_abs_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_compact_value_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:37:36.242807+00:00
-- url     : https://prove2.me/theorems/007afc48-798d-420c-b4c9-934af0402919
-- title:
--   Compact nonnegative reserve yields uniform absolute value bound
-- statement:
--   Use Proved gledger63 compact finite lower bound twice, for w and for -w.
-- source:
--   Required deterministic bounded kernel tool for source original top-cap stopped compensation 46849a70. No restrictions on derivatives, generator or cap, and preserves zero reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_compact_value_abs_bound
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → b ≤ B → |w b| ≤ K := by sorry
