-- Prove2me | Theorems.Thm_CKLaneA3X_TMd_add_good
-- name    : CKLaneA3X.TMd.add_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:50:59.946195+00:00
-- url     : https://prove2.me/theorems/b7d84a91-3e76-4d35-8ae4-75358d2d620d
-- title:
--   Addition preserves A3X Taylor-model enclosures
-- statement:
--   The unchanged source soundness theorem for adding two valid A3X Taylor models, lowering their orders to the same minimum and retaining the exact original rounded remainder.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TMFun.lean#L83

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
import Definitions.Def_A3X_Step028_first_chain

open CKLaneA3X

theorem CKLaneA3X.TMd.add_good {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) :
    Good (fun t ρ => f t ρ + g t ρ) (TMd.add a b) := by sorry
