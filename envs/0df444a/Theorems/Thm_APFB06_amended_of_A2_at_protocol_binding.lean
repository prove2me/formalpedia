-- Prove2me | Theorems.Thm_APFB06_amended_of_A2_at_protocol_binding
-- name    : APFB06.amended_of_A2_at_protocol_binding
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:57:30.454253+00:00
-- url     : https://prove2.me/theorems/a831a241-d911-4b4d-a1d7-16e4aae608c1
-- title:
--   Protocol selection yields an occupancy predicate with explicit bridges
-- statement:
--   For a nonempty family, assume protocol-bound A2, a carrier map on protocols at which every served task is active, and an admitted raw start for every protocol at that carrier. Then a constructed set of alignments satisfies AmendedB06 at the extensional service class and its carrier correspondence. These carrier and start hypotheses remain explicit.
-- source:
--   Sib v44 Theorems/Thm_APFB06_occupancy_from_A2.lean:33

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_at_protocol_binding
    {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : NNReal) (realized : Finset (APFB06.Task Cont Dset) → {p // p ∈ protocols})
    (hA2 : APFB07a.A2Selection (Interface := Finset (APFB06.Task Cont Dset))
      (Configuration := fun _ => {p // p ∈ protocols})
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize (C : ℝ) S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (carrierOf : {p // p ∈ protocols} → APFB01.PhysicalState Cont)
    (hdet : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}),
      APFB07a.Serves maintained sufficient usesToRealize S p →
        ∀ d ∈ S, d.val (carrierOf p) = true)
    (hstart : ∀ p : {p // p ∈ protocols},
      ∃ x : Raw, APFB01.physicalClass Cont x = carrierOf p ∧ Cont x p.val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, o.2.carrier = carrierOf (realized o.2.carried)) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by sorry
