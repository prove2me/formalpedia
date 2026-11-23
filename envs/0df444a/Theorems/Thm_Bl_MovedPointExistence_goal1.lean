-- Prove2me | Theorems.Thm_Bl_MovedPointExistence_goal1
-- name    : Bl.MovedPointExistence.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:26.520799+00:00
-- url     : https://prove2.me/theorems/d5b75a1a-983c-480e-8ce7-e230eb88a391
-- title:
--   Moved Point Existence: goal1
-- statement:
--   The Moved Point Existence construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MovedPointExistence/ExistsMoved.lean#L24-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MovedPointExistence/ExistsMoved.lean#L24-L55

import Mathlib
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open NormedSpace
open Bl Bl.MovedPointExistence
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Bl.MovedPointExistence.goal1 (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by sorry
