-- Prove2me | Theorems.Thm_CKLaneA3X_good_divt
-- name    : CKLaneA3X.good_divt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T05:04:18.280676+00:00
-- url     : https://prove2.me/theorems/52d13abe-dd33-4799-af92-541be5972360
-- title:
--   Division by the positive parameter preserves an A3X enclosure with a vanishing prefix
-- statement:
--   The unchanged source conditional theorem: a valid Taylor-model enclosure with a verified zero constant prefix and order at least one yields an enclosure after dividing its function by the positive domain parameter. The polynomial drops its first row, the remainder is unchanged, and the order decreases by one.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/ExactPoly.lean#L11

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

theorem CKLaneA3X.good_divt {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) (hz : zeroPrefix d.P 1 = true) (hn : 1 ≤ d.n) :
    Good (fun t ρ => f t ρ / t) ⟨TPoly.drop d.P 1, d.r, d.n - 1⟩ := by sorry
