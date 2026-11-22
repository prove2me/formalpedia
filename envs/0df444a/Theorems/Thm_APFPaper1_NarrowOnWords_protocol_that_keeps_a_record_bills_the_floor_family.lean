-- Prove2me | Theorems.Thm_APFPaper1_NarrowOnWords_protocol_that_keeps_a_record_bills_the_floor_family
-- name    : APFPaper1.NarrowOnWords.protocol_that_keeps_a_record_bills_the_floor_family
-- status  : Open
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:55:24.923482+00:00
-- url     : https://prove2.me/theorems/daf44d57-70ad-4d3d-9790-a4eb01b1e022
-- title:
--   protocol that keeps a record bills the floor family
-- statement:
--   Scope and conditions: The protocol bill bound explicitly assumes the guarded MarginalFloor predicate, free null holding, nonnegative capacity, the tested-family record-need condition, that nothing suffices without a record, a uniform positive singleton-cost bound, and maintained records identified with fragmentwise keeping. Applying it to a closed protocol changing the held family or a listed reading additionally assumes RecordedSideStill and actual execution. It supplies no unconditional physical floor or word-to-protocol identification.
--
--   Exact source statement:
--
--   theorem protocol_that_keeps_a_record_bills_the_floor_family (g : Context)
--       {R D : Type*} [DecidableEq D]
--       (protocols : Set (WordFrom Frag g))
--       (resource : WordFrom Frag g → R) (calibration : R → NNReal)
--       (maintained : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g))
--       (sufficient : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g) → D → Prop)
--       (usesToRealize : {p : WordFrom Frag g // p ∈ protocols} → D → Set (Rec g) → Prop)
--       (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
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
--       (p : {p : WordFrom Frag g // p ∈ protocols})
--       (hk : keptByFragments keptFrag g p.val.2 ≠ ∅) :
--       eps ≤ (calibration (resource p.val) : ℝ)
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
--   ['Theorems.Thm_APFPaper5_K2_a_protocol_that_changes_what_is_recorded_bills_the_floor:149; USB pullbacks v58 batch B; SHA-256 a2c16bdc6e6a4ee23f1d84fa94801f68ceb120b75ea80657dd8d998907f8b96d']

import Definitions.Def_APFPaper5_K2_RecordedSideStill
import Theorems.Thm_APFPaper5_K2_change_of_what_is_recorded_needs_a_record
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.Source
section
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
/-- Holding nothing is free: some protocol keeps no record and bills nothing. -/
def HoldingNothingFree : Prop :=
  ∃ p0 : P, maintained p0 = ∅ ∧ (calibration (wholeResource p0) : ℝ) = 0

/-- The empty set of records is sufficient for no distinction. NOT RULED. -/
def NothingSufficesWithoutARecord : Prop :=
  ∀ (p : P) (d : D), ¬ sufficient p ∅ d

/-- The author's sentence of 2026-11-17 16:03 HST with his ruling of 18:25 HST that joint records count,
typed: every record a protocol maintains is kept for some nonempty family of tested distinctions,
within capacity, that the protocol serves, and no protocol that maintains only its other records serves that
family. NOT RULED as the typing. -/
def EveryRecordIsNeededForATestedFamily (tested : D → Prop) (C : ℝ) : Prop :=
  ∀ (p : P) (r : Record), r ∈ maintained p → ∃ S : Finset D, S.Nonempty ∧ (∀ d ∈ S, tested d) ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S ∧
    (∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
    ∀ q : P, maintained q ⊆ maintained p \ {r} →
      ¬ ∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma

/-- What pass 111 uses of the sentence: a protocol that maintains a record serves some tested
distinction that is within capacity alone. -/
def EveryKeeperServesATestedDistinction (tested : D → Prop) (C : ℝ) : Prop :=
  ∀ p : P, (maintained p).Nonempty → ∃ d : D, tested d ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C {d} ∧
    ∃ sigma : Set Record, sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma
end
end APFPaper1.Source
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uK apfNative_u_1 apfNative_u_2

theorem APFPaper1.NarrowOnWords.protocol_that_keeps_a_record_bills_the_floor_family :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] (g : Context) {R : Type apfNative_u_1}
  {D : Type apfNative_u_2} [inst_1 : DecidableEq.{apfNative_u_2 + 1} D]
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
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g)) (tested : D → Prop) (C eps : Real)
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
        protocols p)
  (hk :
    @Ne.{apfNative_uK + 1} (Finset.{apfNative_uK} (Rec g))
      (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst keptFrag
        g g
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
            p)))
      (@EmptyCollection.emptyCollection.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
        (@Finset.instEmptyCollection.{apfNative_uK} (Rec g)))),
  @LE.le.{0} Real Real.instLE eps
    (NNReal.toReal
      (calibration
        (resource
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
            p)))) := by sorry
