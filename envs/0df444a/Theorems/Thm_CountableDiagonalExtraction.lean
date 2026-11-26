-- Prove2me | Theorems.Thm_CountableDiagonalExtraction
-- name    : CountableDiagonalExtraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:09.179821+00:00
-- url     : https://prove2.me/theorems/a8656379-2a6d-4f08-80d6-b9d22c05cdc7
-- title:
--   Countable Diagonal Extraction: Countable Diagonal Extraction
-- statement:
--   Countable diagonal extraction: given, for each index `j` and each stage `l`, a sequence
--   `a j l : ℕ → ℝ` converging as `n → ∞` to a limit `A j` that does NOT depend on `l`, there is a
--   strictly increasing choice `N : ℕ → ℕ` of stage-`l` cutoffs such that the diagonal sequence
--   `l ↦ a j l (N l)` converges to `A j` for every `j`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CountableDiagonalExtraction.lean#L10-L50
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CountableDiagonalExtraction.lean#L10-L50

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_CountableDiagonalExtraction
set_option autoImplicit false
open Filter Topology

theorem CountableDiagonalExtraction
    (a : ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℝ)
    (h : ∀ j l, Tendsto (a j l) atTop (nhds (A j))) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ j, Tendsto (fun l => a j l (N l)) atTop (nhds (A j)) := by sorry
