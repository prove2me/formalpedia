-- Prove2me | Theorems.Thm_CKLaneA3X_TMd_scale_good
-- name    : CKLaneA3X.TMd.scale_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:51:03.277695+00:00
-- url     : https://prove2.me/theorems/4b01aaea-a204-461a-ad54-9fca5d1092fe
-- title:
--   Rational scaling preserves an A3X Taylor-model enclosure
-- statement:
--   The unchanged source soundness theorem for scaling any valid A3X Taylor model by a rational constant, retaining the original absolute-value remainder and upward rounding.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TMFun.lean#L97

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

theorem CKLaneA3X.TMd.scale_good {f : ℝ → ℝ → ℝ} {a : TMd} (ha : Good f a) (c : ℚ) :
    Good (fun t ρ => (c : ℝ) * f t ρ) (TMd.scale c a) := by sorry
