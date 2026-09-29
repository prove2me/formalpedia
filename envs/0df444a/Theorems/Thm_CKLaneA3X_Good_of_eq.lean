-- Prove2me | Theorems.Thm_CKLaneA3X_Good_of_eq
-- name    : CKLaneA3X.Good.of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:47:30.029163+00:00
-- url     : https://prove2.me/theorems/0dc0bf49-a940-4bf7-a1d2-de58c882301a
-- title:
--   Transferring validity to an equal polynomial with a larger remainder
-- statement:
--   A valid Taylor model remains valid when its polynomial and order are equal to the replacement values and its remainder is enlarged. This exact source theorem transfers the checked multiplication result to a stored certificate.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/SeriesTM.lean#L11

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_enclosure

open CKLaneA3X

theorem CKLaneA3X.Good.of_eq {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) {P : TPoly} {r : ℚ} {n : ℕ}
    (hP : d.P = P) (hn : d.n = n) (hr : d.r ≤ r) : Good f ⟨P, r, n⟩ := by sorry
