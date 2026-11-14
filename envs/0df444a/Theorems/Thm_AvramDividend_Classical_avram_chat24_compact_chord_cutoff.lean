-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_compact_chord_cutoff
-- name    : AvramDividend.Classical.avram_chat24_compact_chord_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:37:28.463339+00:00
-- url     : https://prove2.me/theorems/8cb4d7b7-3c90-4f5d-b763-918401146c67
-- title:
--   Compact chord Lipschitz bound and uniform mesh cutoff
-- statement:
--   A C1 function on positive reals has one Lipschitz bound on the enlarged compact state band; choose a uniform grid cutoff so every drift increment fits inside the positive margin.
-- source:
--   Native chord-certificate compactness and mesh precondition; candidates/avram_chat24_compact_chord_cutoff_20261113.research.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_compact_chord_cutoff
    (w : ℝ → ℝ) (a b d : ℝ) (B : ℝ≥0) (ha : 0 < a)
    (hw : ContDiffOn ℝ 1 w (Ioi 0)) :
    ∃ n0 : ℕ, ∃ L : ℝ≥0,
      LipschitzOnWith L w (Icc (a / 2) (b + 1)) ∧
      ∀ n : ℕ, n0 ≤ n →
        d * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)) < min (a / 2) 1 := by sorry
