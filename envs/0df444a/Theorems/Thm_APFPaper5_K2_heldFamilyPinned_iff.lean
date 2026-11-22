-- Prove2me | Theorems.Thm_APFPaper5_K2_heldFamilyPinned_iff
-- name    : APFPaper5.K2.heldFamilyPinned_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:07:21.4318+00:00
-- url     : https://prove2.me/theorems/5322b21d-dfd8-4c91-a477-b480e55384e9
-- title:
--   heldFamilyPinned iff
-- statement:
--   Scope and conditions: HeldFamilyPinned preserves true listed readings under record-free closed words. The hold word's assumed admitted record-free inverse yields preservation of both sides. Covering the list then preserves the held family and recorded class; separation is additionally required for raw-state identity, and EveryCombinationHeld with injective listing for trivial permutation/flips. This does not constrain unrecorded held data or establish physical hold reversibility.
--
--   Exact source statement:
--
--   theorem heldFamilyPinned_iff (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g)) :
--       HeldFamilyPinned step keptFrag reads listed ↔
--         ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g),
--           keptByFragments keptFrag g W = ∅ → Executes step W x y → d ∈ listed g →
--             reads g d x = true → reads g d y = true
--
--   Source parameters:
--
--   universe uI uC uF uX uR uK uD uW
--   variable {ι : Type uI}
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_no_hold_on_the_recorded_side:168; USB pullbacks v58 batch B; SHA-256 e78180714928800eb3093d785d8aceec46f82e90caaef3c7fa5b6b23e55f9e4c']

import Definitions.Def_APFPaper5_K2_HeldFamilyPinned
import Definitions.Def_APFPaper5_K2_HoldWord
import Theorems.Thm_APFPaper5_K2_executesAs_unique
import Theorems.Thm_APFPaper5_K2_rearrangement_unique
import Theorems.Thm_APFPaper5_K2_mem_heldFamily_r2
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uX apfNative_uK apfNative_uD

theorem APFPaper5.K2.heldFamilyPinned_iff :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {Rec : Context → Type apfNative_uK} [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)]
  {Dn : Context → Type apfNative_uD} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g)),
  Iff
    (@APFPaper5.K2.HeldFamilyPinned.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed)
    (∀ (g : Context) (W : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g g) (x y : Raw g)
      (d : Dn g),
      @Eq.{apfNative_uK + 1} (Finset.{apfNative_uK} (Rec g))
          (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst
            keptFrag g g g W)
          (@EmptyCollection.emptyCollection.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
            (@Finset.instEmptyCollection.{apfNative_uK} (Rec g))) →
        @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g g W x y →
          @Membership.mem.{apfNative_uD, apfNative_uD} (Dn g) (Finset.{apfNative_uD} (Dn g))
              (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn g)) (Dn g)
                (@Finset.instSetLike.{apfNative_uD} (Dn g)))
              (listed g) d →
            @Eq.{1} Bool (reads g d x) Bool.true → @Eq.{1} Bool (reads g d y) Bool.true) := by sorry
