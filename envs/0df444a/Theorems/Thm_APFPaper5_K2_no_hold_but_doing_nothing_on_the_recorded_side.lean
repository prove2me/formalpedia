-- Prove2me | Theorems.Thm_APFPaper5_K2_no_hold_but_doing_nothing_on_the_recorded_side
-- name    : APFPaper5.K2.no_hold_but_doing_nothing_on_the_recorded_side
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:40:29.886055+00:00
-- url     : https://prove2.me/theorems/662093ff-0a1e-45e5-9267-355500badf92
-- title:
--   no hold but doing nothing on the recorded side
-- statement:
--   Scope and conditions: HeldFamilyPinned preserves true listed readings under record-free closed words. The hold word's assumed admitted record-free inverse yields preservation of both sides. Covering the list then preserves the held family and recorded class; separation is additionally required for raw-state identity, and EveryCombinationHeld with injective listing for trivial permutation/flips. This does not constrain unrecorded held data or establish physical hold reversibility.
--
--   Exact source statement:
--
--   theorem no_hold_but_doing_nothing_on_the_recorded_side
--       (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
--       (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
--       (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
--       (hlisted : ∀ i, dist i ∈ listed a) (hcover : ∀ d ∈ listed a, ∃ i, dist i = d)
--       (hsep : ∀ x y : Raw a, (∀ d ∈ listed a, reads a d y = reads a d x) → y = x)
--       (hcomb : APFB02.EveryCombinationHeld (reads a)) (hinj : Function.Injective dist) :
--       sigma = Equiv.refl ι ∧ (flip = fun _ => false) ∧
--         ∀ h : Raw a → Raw a, ExecutesAs step W h → ∀ x : Raw a, h x = x
--
--   Source parameters:
--
--   universe uI uC uF uX uR uK uD uW
--   variable {ι : Type uI}
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--     {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_no_hold_on_the_recorded_side:313; USB pullbacks v58 batch B; SHA-256 e78180714928800eb3093d785d8aceec46f82e90caaef3c7fa5b6b23e55f9e4c']

import Definitions.Def_APFPaper5_K2_HeldFamilyPinned
import Definitions.Def_APFPaper5_K2_HoldWord
import Theorems.Thm_APFPaper5_K2_executesAs_unique
import Theorems.Thm_APFPaper5_K2_rearrangement_unique
import Theorems.Thm_APFPaper5_K2_mem_heldFamily_r2
set_option autoImplicit false
universe apfNative_uI apfNative_uC apfNative_uF apfNative_uX apfNative_uK apfNative_uD

theorem APFPaper5.K2.no_hold_but_doing_nothing_on_the_recorded_side :
∀ {ι : Type apfNative_uI} {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF}
  {Raw : Context → Type apfNative_uX} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] {Dn : Context → Type apfNative_uD}
  (Defd : (g : Context) → Raw g → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Prop)
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (hP :
    @APFPaper5.K2.HeldFamilyPinned.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed)
  {a : Context} (W : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a) (dist : ι → Dn a)
  (G : ι → ι → Real) (sigma : Equiv.Perm.{apfNative_uI + 1} ι) (flip : ι → Bool)
  (hW :
    @APFPaper5.K2.IsHoldWord.{apfNative_uI, apfNative_uD, apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK} ι
      Context Frag Raw Rec Defd
      (@APFPaper1.Continuation.keepsFW.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst keptFrag) step a
      W (Dn a) (reads a) dist G sigma flip)
  (hlisted :
    ∀ (i : ι),
      @Membership.mem.{apfNative_uD, apfNative_uD} (Dn a) (Finset.{apfNative_uD} (Dn a))
        (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn a)) (Dn a)
          (@Finset.instSetLike.{apfNative_uD} (Dn a)))
        (listed a) (dist i))
  (hcover :
    ∀ (d : Dn a),
      @Membership.mem.{apfNative_uD, apfNative_uD} (Dn a) (Finset.{apfNative_uD} (Dn a))
          (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn a)) (Dn a)
            (@Finset.instSetLike.{apfNative_uD} (Dn a)))
          (listed a) d →
        @Exists.{apfNative_uI + 1} ι fun (i : ι) => @Eq.{apfNative_uD + 1} (Dn a) (dist i) d)
  (hsep :
    ∀ (x y : Raw a),
      (∀ (d : Dn a),
          @Membership.mem.{apfNative_uD, apfNative_uD} (Dn a) (Finset.{apfNative_uD} (Dn a))
              (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn a)) (Dn a)
                (@Finset.instSetLike.{apfNative_uD} (Dn a)))
              (listed a) d →
            @Eq.{1} Bool (reads a d y) (reads a d x)) →
        @Eq.{apfNative_uX + 1} (Raw a) y x)
  (hcomb : @APFB02.EveryCombinationHeld.{apfNative_uX, apfNative_uD} (Raw a) (Dn a) (reads a))
  (hinj : @Function.Injective.{apfNative_uI + 1, apfNative_uD + 1} ι (Dn a) dist),
  And (@Eq.{apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) sigma (Equiv.refl.{apfNative_uI + 1} ι))
    (And (@Eq.{apfNative_uI + 1} (ι → Bool) flip fun (x : ι) => Bool.false)
      (∀ (h : Raw a → Raw a),
        @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step a W h →
          ∀ (x : Raw a), @Eq.{apfNative_uX + 1} (Raw a) (h x) x)) := by sorry
