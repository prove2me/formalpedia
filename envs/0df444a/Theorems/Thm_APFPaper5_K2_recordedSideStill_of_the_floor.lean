-- Prove2me | Theorems.Thm_APFPaper5_K2_recordedSideStill_of_the_floor
-- name    : APFPaper5.K2.recordedSideStill_of_the_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T20:04:14.240264+00:00
-- url     : https://prove2.me/theorems/e4c6e7d6-ed95-4018-8391-06290b45f46a
-- title:
--   recordedSideStill of the floor
-- statement:
--   Scope and conditions: RecordedSideStill is equivalent to true-side pinning together with NoFreeGain. Pinning yields no free gain when every record-free closed execution has a record-free return; that return is a premise. With FreeOnWords and a record floor, recorded stillness is equivalent to the positive recorded-change floor. Stillness preserves held families and recorded classes; fixing raw states additionally requires list separation. These results neither identify physical records nor supply physical reversibility.
--
--   Exact source statement:
--
--   theorem recordedSideStill_of_the_floor
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (resource : (g : Context) → WordFrom Frag g → R g)
--       (calibration : (g : Context) → R g → NNReal)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
--       (hC : ChangingARecordedSideCostsTheFloor step resource calibration reads listed eps) :
--       RecordedSideStill step keptFrag reads listed
--
--   Source parameters:
--
--   universe uC uF uX uR uK uD uW
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded:220; USB pullbacks v58 batch B; SHA-256 bb46d3ad94f1f311b1e929628f87ed08d93697aa7f1105d1990ec9bdf398f82c']

import Definitions.Def_APFPaper5_K2_RecordedSideStill
import Theorems.Thm_APFPaper5_K2_heldFamilyPinned_iff
import Theorems.Thm_APFPaper5_K2_heldFamilyPinned_of_the_floor_by_sides
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_every_listed_side
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_the_held_family
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_the_recorded_class
import Theorems.Thm_APFPaper5_K2_holdWord_does_nothing_on_the_recorded_side
import Theorems.Thm_APFPaper5_K2_holdWord_rearrangement_trivial_on_the_recorded_side
import Theorems.Thm_APFPaper5_K2_no_hold_but_doing_nothing_on_the_recorded_side
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uK apfNative_uD

theorem APFPaper5.K2.recordedSideStill_of_the_floor :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] {Dn : Context → Type apfNative_uD}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (eps : Context → NNReal)
  (hfree :
    @APFB06.FreeOnWords.{apfNative_uC, apfNative_uF, apfNative_uR, apfNative_uK} Context Frag R Rec inst resource
      calibration keptFrag)
  (hC :
    @APFPaper5.K2.ChangingARecordedSideCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR,
          apfNative_uD}
      Context Frag Raw R Dn step resource calibration reads listed eps),
  @APFPaper5.K2.RecordedSideStill.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
    Raw Rec inst Dn step keptFrag reads listed := by sorry
