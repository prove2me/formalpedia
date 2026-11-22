-- Prove2me | Theorems.Thm_APFPaper5_K2_heldFamilyPinned_of_the_floor_by_sides
-- name    : APFPaper5.K2.heldFamilyPinned_of_the_floor_by_sides
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:10:18.810216+00:00
-- url     : https://prove2.me/theorems/db8dc48a-72fc-4435-a73f-99fa70b2b842
-- title:
--   heldFamilyPinned of the floor by sides
-- statement:
--   Scope and conditions: HeldFamilyPinned preserves true listed readings under record-free closed words. The hold word's assumed admitted record-free inverse yields preservation of both sides. Covering the list then preserves the held family and recorded class; separation is additionally required for raw-state identity, and EveryCombinationHeld with injective listing for trivial permutation/flips. This does not constrain unrecorded held data or establish physical hold reversibility.
--
--   Exact source statement:
--
--   theorem heldFamilyPinned_of_the_floor_by_sides
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (resource : (g : Context) → WordFrom Frag g → R g)
--       (calibration : (g : Context) → R g → NNReal)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
--       (hS : TurningAHeldSideCostsTheFloor step resource calibration reads
--         (fun g x d => d ∈ heldFamily (reads g) (listed g) x) eps) :
--       HeldFamilyPinned step keptFrag reads listed
--
--   Source parameters:
--
--   universe uI uC uF uX uR uK uD uW
--   variable {ι : Type uI}
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_no_hold_on_the_recorded_side:186; USB pullbacks v58 batch B; SHA-256 e78180714928800eb3093d785d8aceec46f82e90caaef3c7fa5b6b23e55f9e4c']

import Definitions.Def_APFPaper5_K2_HeldFamilyPinned
import Definitions.Def_APFPaper5_K2_HoldWord
import Theorems.Thm_APFPaper5_K2_executesAs_unique
import Theorems.Thm_APFPaper5_K2_rearrangement_unique
import Theorems.Thm_APFPaper5_K2_mem_heldFamily_r2
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uK apfNative_uD

theorem APFPaper5.K2.heldFamilyPinned_of_the_floor_by_sides :
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
  (hS :
    @APFPaper1.NarrowOnWords.TurningAHeldSideCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR,
          apfNative_uD}
      Context Frag Raw R Dn step resource calibration reads
      (fun (g : Context) (x : Raw g) (d : Dn g) =>
        @Membership.mem.{apfNative_uD, apfNative_uD} (Dn g) (Finset.{apfNative_uD} (Dn g))
          (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn g)) (Dn g)
            (@Finset.instSetLike.{apfNative_uD} (Dn g)))
          (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} (Raw g) (Dn g) (reads g) (listed g) x) d)
      eps),
  @APFPaper5.K2.HeldFamilyPinned.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag Raw
    Rec inst Dn step keptFrag reads listed := by sorry
