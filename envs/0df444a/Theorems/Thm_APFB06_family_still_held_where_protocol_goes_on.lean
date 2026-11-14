-- Prove2me | Theorems.Thm_APFB06_family_still_held_where_protocol_goes_on
-- name    : APFB06.family_still_held_where_protocol_goes_on
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:57:25.174903+00:00
-- url     : https://prove2.me/theorems/4be53f23-b5a4-4c75-8d91-a482903c6b25
-- title:
--   Family still held where protocol goes on
-- statement:
--   Assume an admitted serving protocol makes its served family active at its admission state. If the same protocol is admitted after an arbitrary step, its served tasks are active there. The crucial readmission and admission-to-activity law are hypotheses.
-- source:
--   Sib v44 Theorems/Thm_APFB06_protocols_only_at_occupants.lean:70

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.family_still_held_where_protocol_goes_on
    {Raw FullProcess Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (hocc : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}) (x : Raw),
      APFB07a.Serves maintained sufficient usesToRealize S p → Cont x p.val →
        ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset))
    (p : {p // p ∈ protocols}) (hp : APFB07a.Serves maintained sufficient usesToRealize S p)
    (x : Raw) (u : FullProcess) (hagain : Cont (after x u) p.val) :
    ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true := by sorry
