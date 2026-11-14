-- Prove2me | Theorems.Thm_APFB06_amended_of_A2_and_occupant_alignment
-- name    : APFB06.amended_of_A2_and_occupant_alignment
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:55:39.638754+00:00
-- url     : https://prove2.me/theorems/3166a207-dc9f-46f7-af97-88574a156cb2
-- title:
--   Protocol selection and supplied occupants yield an occupancy predicate
-- statement:
--   Assume protocol-bound A2, a supplied occupant alignment for every family with exactly that carried family, and an admitted raw start of the realized protocol at that carrier. For every nonempty family a constructed singleton of those occupants satisfies AmendedB06 at the extensional service class. This does not prove post-execution preservation or source actuality.
-- source:
--   Sib v44 Theorems/Thm_APFB06_occupant_alignment_holds.lean:56

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_and_occupant_alignment
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
    (occupant : Finset (APFB06.Task Cont Dset) → APFB06.OriginalAlignment Cont Dset)
    (hfam : ∀ S : Finset (APFB06.Task Cont Dset), (occupant S).carried = S)
    (hstart : ∀ S : Finset (APFB06.Task Cont Dset),
      ∃ x : Raw, APFB01.physicalClass Cont x = (occupant S).carrier ∧ Cont x (realized S).val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, ∃ T : Finset (APFB06.Task Cont Dset), o.2 = occupant T) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by sorry
