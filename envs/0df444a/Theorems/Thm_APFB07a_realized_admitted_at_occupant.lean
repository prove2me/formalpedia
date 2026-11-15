-- Prove2me | Theorems.Thm_APFB07a_realized_admitted_at_occupant
-- name    : APFB07a.realized_admitted_at_occupant
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:04:59.439246+00:00
-- url     : https://prove2.me/theorems/c21e702c-6de2-410e-ab15-72bb53851cf5
-- title:
--   Realized admitted at occupant
-- statement:
--   If A2Selection holds with occupantAdmissible as its domain at every supplied alignment/raw-state interface, its selected protocol is admitted at that raw state, serves the alignment’s entire family, and has bill at most capacity. This is extraction of the admissibility conjunct at a supplied domain binding.
-- source:
--   Sib v44 Theorems/Thm_APFB06_occupancy_at_occupant_binding.lean:28

import Definitions.Def_APFB07a_OccupantBinding

set_option autoImplicit false

theorem APFB07a.realized_admitted_at_occupant
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
      APFB01.physicalClass Cont ox.2 = ox.1.carrier}) :
    Cont i.val.2 (realized i).val ∧
      APFB07a.Serves maintained sufficient usesToRealize i.val.1.carried (realized i) ∧
      APFB07a.protocolBill wholeResource calibration (realized i) ≤ (C : ℝ) := by sorry
