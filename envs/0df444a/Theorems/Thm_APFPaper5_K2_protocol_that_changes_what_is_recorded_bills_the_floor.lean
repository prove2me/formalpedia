-- Prove2me | Theorems.Thm_APFPaper5_K2_protocol_that_changes_what_is_recorded_bills_the_floor
-- name    : APFPaper5.K2.protocol_that_changes_what_is_recorded_bills_the_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-23T01:05:31.672583+00:00
-- url     : https://prove2.me/theorems/fd39924b-f748-4225-b2d7-8d78f265be3e
-- title:
--   protocol that changes what is recorded bills the floor
-- statement:
--   Scope and conditions: The protocol bill bound explicitly assumes the guarded MarginalFloor predicate, free null holding, nonnegative capacity, the tested-family record-need condition, that nothing suffices without a record, a uniform positive singleton-cost bound, and maintained records identified with fragmentwise keeping. Applying it to a closed protocol changing the held family or a listed reading additionally assumes RecordedSideStill and actual execution. It supplies no unconditional physical floor or word-to-protocol identification.
--
--   Exact source statement:
--
--   theorem protocol_that_changes_what_is_recorded_bills_the_floor
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
--       (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
--       (hS : RecordedSideStill step keptFrag reads listed)
--       (g : Context) {R D : Type*} [DecidableEq D]
--       (protocols : Set (WordFrom Frag g))
--       (resource : WordFrom Frag g → R) (calibration : R → NNReal)
--       (maintained : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g))
--       (sufficient : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g) → D → Prop)
--       (usesToRealize : {p : WordFrom Frag g // p ∈ protocols} → D → Set (Rec g) → Prop)
--       (tested : D → Prop) (C eps : ℝ)
--       (hmaint : ∀ p : {p : WordFrom Frag g // p ∈ protocols},
--         maintained p = (↑(keptByFragments keptFrag g p.val.2) : Set (Rec g)))
--       (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D)
--         (P := fun _ => {p : WordFrom Frag g // p ∈ protocols})
--         (R := fun _ => R) (Record := fun _ => Rec g) (fun _ p => resource p.val)
--         (fun _ => calibration) (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize)
--         (fun _ => tested) (fun _ => C) (fun _ => eps))
--       (hfree : HoldingNothingFree
--         (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained)
--       (hC : 0 ≤ C)
--       (hF : EveryRecordIsNeededForATestedFamily
--         (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
--         sufficient usesToRealize tested C)
--       (hnon : NothingSufficesWithoutARecord
--         (P := {p : WordFrom Frag g // p ∈ protocols}) sufficient)
--       (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D, eta ≤ familyCost
--         (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
--         sufficient usesToRealize {d})
--       (W : Word Frag g g) (hp : (⟨g, W⟩ : WordFrom Frag g) ∈ protocols) (x y : Raw g)
--       (hex : Executes step W x y)
--       (hne : heldFamily (reads g) (listed g) y ≠ heldFamily (reads g) (listed g) x) :
--       eps ≤ (calibration (resource ⟨g, W⟩) : ℝ)
--
--   Source parameters:
--
--   universe uC uF uK
--   variable {Context : Type uC} {Frag : Context → Context → Type uF}
--     {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
--   universe uC uF uX uK uD
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)] {Dn : Context → Type uD}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_a_protocol_that_changes_what_is_recorded_bills_the_floor:198; USB pullbacks v58 batch B; SHA-256 a2c16bdc6e6a4ee23f1d84fa94801f68ceb120b75ea80657dd8d998907f8b96d']

import Theorems.Thm_APFPaper1_NarrowOnWords_protocol_that_keeps_a_record_bills_the_floor_family
import Definitions.Def_APFPaper5_K2_RecordedSideStill
import Theorems.Thm_APFPaper5_K2_change_of_what_is_recorded_needs_a_record
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uX apfNative_uK apfNative_uD apfNative_u_1 apfNative_u_2

theorem APFPaper5.K2.protocol_that_changes_what_is_recorded_bills_the_floor :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {Rec : Context → Type apfNative_uK} [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)]
  {Dn : Context → Type apfNative_uD} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (hS :
    @APFPaper5.K2.RecordedSideStill.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed)
  (g : Context) {R : Type apfNative_u_1} {D : Type apfNative_u_2} [inst_1 : DecidableEq.{apfNative_u_2 + 1} D]
  (protocols :
    Set.{max apfNative_uF apfNative_uC} (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
  (resource : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R)
  (calibration : R → NNReal)
  (maintained :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      Set.{apfNative_uK} (Rec g))
  (sufficient :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      Set.{apfNative_uK} (Rec g) → D → Prop)
  (usesToRealize :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      D → Set.{apfNative_uK} (Rec g) → Prop)
  (tested : D → Prop) (C eps : Real)
  (hmaint :
    ∀
      (p :
        @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
          @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (Set.{max apfNative_uF apfNative_uC}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            (@Set.instMembership.{max apfNative_uC apfNative_uF}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            protocols p),
      @Eq.{apfNative_uK + 1} (Set.{apfNative_uK} (Rec g)) (maintained p)
        (@SetLike.coe.{apfNative_uK, apfNative_uK} (Finset.{apfNative_uK} (Rec g)) (Rec g)
          (@Finset.instSetLike.{apfNative_uK} (Rec g))
          (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst
            keptFrag g g
            (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
              (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                  @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (Set.{max apfNative_uF apfNative_uC}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    (@Set.instMembership.{max apfNative_uC apfNative_uF}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    protocols p)
                p))
            (@Sigma.snd.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
              (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                  @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (Set.{max apfNative_uF apfNative_uC}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    (@Set.instMembership.{max apfNative_uC apfNative_uF}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    protocols p)
                p)))))
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK} Unit
      (fun (x : Unit) => D)
      (fun (x : Unit) =>
        @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
          @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (Set.{max apfNative_uF apfNative_uC}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            (@Set.instMembership.{max apfNative_uC apfNative_uF}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            protocols p)
      (fun (x : Unit) => R) (fun (x : Unit) => Rec g) (fun (g : Unit) => inst_1)
      (fun (x : Unit)
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      (fun (x : Unit) => calibration) (fun (x : Unit) => maintained) (fun (x : Unit) => sufficient)
      (fun (x : Unit) => usesToRealize) (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (hfree :
    @APFPaper1.Source.HoldingNothingFree.{max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK}
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      R (Rec g)
      (fun
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      calibration maintained)
  (hC : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
  (hF :
    @APFPaper1.Source.EveryRecordIsNeededForATestedFamily.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1,
          apfNative_uK}
      D
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      R (Rec g)
      (fun
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      calibration maintained sufficient usesToRealize tested C)
  (hnon :
    @APFPaper1.Source.NothingSufficesWithoutARecord.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_uK} D
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      (Rec g) sufficient)
  (hunif :
    @Exists.{1} Real fun (eta : Real) =>
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eta)
        (∀ (d : D),
          @LE.le.{0} Real Real.instLE eta
            (@APFPaper1.Source.familyCost.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK} D
              (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                  (Set.{max apfNative_uF apfNative_uC}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                  (@Set.instMembership.{max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                  protocols p)
              R (Rec g)
              (fun
                  (p :
                    @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                      fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                      @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                        (Set.{max apfNative_uF apfNative_uC}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        (@Set.instMembership.{max apfNative_uC apfNative_uF}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        protocols p) =>
                resource
                  (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                      @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                        (Set.{max apfNative_uF apfNative_uC}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        (@Set.instMembership.{max apfNative_uC apfNative_uF}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        protocols p)
                    p))
              calibration maintained sufficient usesToRealize
              (@Singleton.singleton.{apfNative_u_2, apfNative_u_2} D (Finset.{apfNative_u_2} D)
                (@Finset.instSingleton.{apfNative_u_2} D) d))))
  (W : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g g)
  (hp :
    @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
      (@Sigma.{apfNative_uC, max apfNative_uC apfNative_uF} Context fun (h : Context) =>
        @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
      (Set.{max apfNative_uF apfNative_uC}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
      (@Set.instMembership.{max apfNative_uC apfNative_uF}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
      protocols
      (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
        (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) g W))
  (x y : Raw g)
  (hex : @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g g W x y)
  (hne :
    @Ne.{apfNative_uD + 1} (Finset.{apfNative_uD} (Dn g))
      (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} (Raw g) (Dn g) (reads g) (listed g) y)
      (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} (Raw g) (Dn g) (reads g) (listed g) x)),
  @LE.le.{0} Real Real.instLE eps
    (NNReal.toReal
      (calibration
        (resource
          (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
            (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) g W)))) := by sorry
