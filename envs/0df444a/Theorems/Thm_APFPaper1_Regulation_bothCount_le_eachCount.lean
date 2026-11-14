-- Prove2me | Theorems.Thm_APFPaper1_Regulation_bothCount_le_eachCount
-- name    : APFPaper1.Regulation.bothCount_le_eachCount
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:22:55.684954+00:00
-- url     : https://prove2.me/theorems/728afd57-177e-4877-80d5-6c337bec12cf
-- title:
--   Jointly-held list counts never exceed individual counts
-- statement:
--   For every supplied disturbance list and pair of marks, the count of jointly-holdable occurrences is at most the count where both marks are individually holdable. One joint witness gives both individual witnesses, while the converse is not assumed. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_pair.lean, declaration at line 71 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APFPaper1_RegulationCounts
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
open APFPaper1.Regulation
open APFPaper1.Continuation
open Classical

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem APFPaper1.Regulation.bothCount_le_eachCount (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    bothCount step resource calibration C reads g xs m1 m2 ≤
      eachCount step resource calibration C reads g xs m1 m2 := by sorry
