-- Prove2me | Theorems.Thm_CKLaneA3X_TMd_mul_good
-- name    : CKLaneA3X.TMd.mul_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:47:33.927601+00:00
-- url     : https://prove2.me/theorems/97b50bc0-d43e-40c9-9854-5ca95baf6b9a
-- title:
--   Validity of A3X Taylor-model multiplication
-- statement:
--   If two Taylor-model records are valid enclosures of two functions and their vanishing-prefix and order conditions hold, the original truncated multiplication operation is a valid enclosure of the product function.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TMFun.lean#L62

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

theorem CKLaneA3X.TMd.mul_good {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) (va vb n : ℕ)
    (hza : zeroPrefix a.P va = true) (hzb : zeroPrefix b.P vb = true)
    (hva : va ≤ a.n) (hn1 : n ≤ va + b.n) (hn2 : n ≤ vb + a.n) :
    Good (fun t ρ => f t ρ * g t ρ) (TMd.mul a b va vb n) := by sorry
