-- Prove2me | Theorems.Thm_APFPaper5_K2_changing_costs_the_floor_of_still
-- name    : APFPaper5.K2.changing_costs_the_floor_of_still
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:52:56.358392+00:00
-- url     : https://prove2.me/theorems/065d0be6-afb3-46b5-9eb0-b097f70e1e3f
-- title:
--   changing costs the floor of still
-- statement:
--   Scope and conditions: RecordedSideStill is equivalent to true-side pinning together with NoFreeGain. Pinning yields no free gain when every record-free closed execution has a record-free return; that return is a premise. With FreeOnWords and a record floor, recorded stillness is equivalent to the positive recorded-change floor. Stillness preserves held families and recorded classes; fixing raw states additionally requires list separation. These results neither identify physical records nor supply physical reversibility.
--
--   Exact source statement:
--
--   theorem changing_costs_the_floor_of_still
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (resource : (g : Context) → WordFrom Frag g → R g)
--       (calibration : (g : Context) → R g → NNReal)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (eps : Context → NNReal) (hM : MakingARecordCostsTheFloor resource calibration keptFrag eps)
--       (hS : RecordedSideStill step keptFrag reads listed) :
--       ChangingARecordedSideCostsTheFloor step resource calibration reads listed eps
--
--   Source parameters:
--
--   universe uC uF uX uR uK uD uW
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded:237; USB pullbacks v58 batch B; SHA-256 bb46d3ad94f1f311b1e929628f87ed08d93697aa7f1105d1990ec9bdf398f82c']

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

theorem APFPaper5.K2.changing_costs_the_floor_of_still :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] {Dn : Context → Type apfNative_uD}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (eps : Context → NNReal)
  (hM :
    @APFPaper1.NarrowOnWords.MakingARecordCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uR, apfNative_uK} Context
      Frag R Rec inst resource calibration keptFrag eps)
  (hS :
    @APFPaper5.K2.RecordedSideStill.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed),
  @APFPaper5.K2.ChangingARecordedSideCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR,
        apfNative_uD}
    Context Frag Raw R Dn step resource calibration reads listed eps := by sorry
