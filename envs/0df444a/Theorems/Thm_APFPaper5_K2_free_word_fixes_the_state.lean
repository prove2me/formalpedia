-- Prove2me | Theorems.Thm_APFPaper5_K2_free_word_fixes_the_state
-- name    : APFPaper5.K2.free_word_fixes_the_state
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:53:07.904901+00:00
-- url     : https://prove2.me/theorems/732f6b88-411e-45e8-aeb3-1da3bca20023
-- title:
--   free word fixes the state
-- statement:
--   Scope and conditions: RecordedSideStill is equivalent to true-side pinning together with NoFreeGain. Pinning yields no free gain when every record-free closed execution has a record-free return; that return is a premise. With FreeOnWords and a record floor, recorded stillness is equivalent to the positive recorded-change floor. Stillness preserves held families and recorded classes; fixing raw states additionally requires list separation. These results neither identify physical records nor supply physical reversibility.
--
--   Exact source statement:
--
--   theorem free_word_fixes_the_state
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (hS : RecordedSideStill step keptFrag reads listed) (g : Context)
--       (hsep : ∀ x y : Raw g, (∀ d ∈ listed g, reads g d y = reads g d x) → y = x)
--       (W : Word Frag g g) (x y : Raw g) (hk : keptByFragments keptFrag g W = ∅)
--       (hex : Executes step W x y) : y = x
--
--   Source parameters:
--
--   universe uC uF uX uR uK uD uW
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded:296; USB pullbacks v58 batch B; SHA-256 bb46d3ad94f1f311b1e929628f87ed08d93697aa7f1105d1990ec9bdf398f82c']

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
universe apfNative_uC apfNative_uF apfNative_uX apfNative_uK apfNative_uD

theorem APFPaper5.K2.free_word_fixes_the_state :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {Rec : Context → Type apfNative_uK} [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)]
  {Dn : Context → Type apfNative_uD} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (hS :
    @APFPaper5.K2.RecordedSideStill.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed)
  (g : Context)
  (hsep :
    ∀ (x y : Raw g),
      (∀ (d : Dn g),
          @Membership.mem.{apfNative_uD, apfNative_uD} (Dn g) (Finset.{apfNative_uD} (Dn g))
              (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn g)) (Dn g)
                (@Finset.instSetLike.{apfNative_uD} (Dn g)))
              (listed g) d →
            @Eq.{1} Bool (reads g d y) (reads g d x)) →
        @Eq.{apfNative_uX + 1} (Raw g) y x)
  (W : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g g) (x y : Raw g)
  (hk :
    @Eq.{apfNative_uK + 1} (Finset.{apfNative_uK} (Rec g))
      (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst keptFrag
        g g g W)
      (@EmptyCollection.emptyCollection.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
        (@Finset.instEmptyCollection.{apfNative_uK} (Rec g))))
  (hex : @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g g W x y),
  @Eq.{apfNative_uX + 1} (Raw g) y x := by sorry
