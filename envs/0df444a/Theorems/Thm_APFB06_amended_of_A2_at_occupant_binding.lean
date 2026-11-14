-- Prove2me | Theorems.Thm_APFB06_amended_of_A2_at_occupant_binding
-- name    : APFB06.amended_of_A2_at_occupant_binding
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:10.595991+00:00
-- url     : https://prove2.me/theorems/f4e0dbc7-438f-46df-9000-b959c8623333
-- title:
--   Occupant-bound selection yields the amended occupancy predicate
-- statement:
--   Under A2Selection at the occupant-bound protocol domain and a supplied interface whose carried family is nonempty, AmendedB06 holds on the singleton containing that alignment, with the joint class defined by service. The candidate domain already requires admission at the occupant; no identification of the singleton with physical irreducibly joint occurrences is proved.
-- source:
--   Sib v44 Theorems/Thm_APFB06_occupancy_at_occupant_binding.lean:52

import Definitions.Def_APFB07a_OccupantBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_at_occupant_binding
    {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : NNReal)
    (realized : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier} → {p // p ∈ protocols})
    (hA2 : APFB07a.A2Selection
      (Interface := {ox : APFB06.OriginalAlignment Cont Dset × Raw //
        APFB01.physicalClass Cont ox.2 = ox.1.carrier})
      (Configuration := fun _ => {p // p ∈ protocols})
      (fun i p => APFB07a.occupantAdmissible Cont Dset protocols wholeResource calibration
        maintained sufficient usesToRealize (C : ℝ) i.val.1 i.val.2 p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (i : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier})
    (hS : i.val.1.carried.Nonempty) :
    APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
      (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
      (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
      (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
      (fun _ => wholeResource) (fun _ => calibration) (fun _ => C)
      ({⟨(), i.val.1⟩} : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset)) := by sorry
