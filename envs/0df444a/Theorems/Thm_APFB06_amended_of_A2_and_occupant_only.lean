-- Prove2me | Theorems.Thm_APFB06_amended_of_A2_and_occupant_only
-- name    : APFB06.amended_of_A2_and_occupant_only
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:11.325345+00:00
-- url     : https://prove2.me/theorems/1624213f-d46b-4cf6-840d-f08369551d1e
-- title:
--   Admission-to-activity assumptions yield an occupancy predicate
-- statement:
--   Assume protocol-bound A2, admission of every realized protocol somewhere, and that an admitted serving protocol has every served task active at its start class. For each nonempty family, a constructed set of alignments satisfies AmendedB06 at the extensional service class. The admission-to-activity and existence assumptions are not derived.
-- source:
--   Sib v44 Theorems/Thm_APFB06_protocols_only_at_occupants.lean:32

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_and_occupant_only
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
    (hocc : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}) (x : Raw),
      APFB07a.Serves maintained sufficient usesToRealize S p → Cont x p.val →
        ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (hinst : ∀ S : Finset (APFB06.Task Cont Dset), ∃ x : Raw, Cont x (realized S).val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, ∃ x : Raw, o.2.carrier = APFB01.physicalClass Cont x ∧
        Cont x (realized o.2.carried).val) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by sorry
