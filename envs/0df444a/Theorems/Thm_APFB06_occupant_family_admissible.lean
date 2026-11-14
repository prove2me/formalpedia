-- Prove2me | Theorems.Thm_APFB06_occupant_family_admissible
-- name    : APFB06.occupant_family_admissible
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:58:06.125382+00:00
-- url     : https://prove2.me/theorems/b16bd36a-5aad-4b7c-bf41-9089a2df2611
-- title:
--   Occupant family admissible
-- statement:
--   B06 at the extensional class gives an actual nonempty occupant with every carried subfamily ledger-admissible, and one serving whole protocol available at a raw input.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFB06_ExtensionalJoint
import Theorems.Thm_APFB06_occupant_subfamily_cost
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false
open APFPaper1.Source

namespace APFB06
end APFB06
open APFB06

theorem APFB06.occupant_family_admissible
    {Context : Type*} {Raw FullProcess Resource : Context → Type*} {Record : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (maintained : (g : Context) → {p // p ∈ protocols g} → Set (Record g))
    (sufficient : (g : Context) → {p // p ∈ protocols g} → Set (Record g) →
      Task (Cont g) (D g) → Prop)
    (usesToRealize : (g : Context) → {p // p ∈ protocols g} → Task (Cont g) (D g) →
      Set (Record g) → Prop)
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (hB06 : AmendedB06_20260914 Cont D protocols
      (fun g => extensionalJoint (maintained g) (sufficient g) (usesToRealize g))
      wholeResource calibration C actualJoint) :
    ∃ o : Sigma fun g => OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      (∀ S' : Finset (Task (Cont o.1) (D o.1)), S' ⊆ o.2.carried →
        familyAdmissible (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
          (usesToRealize o.1) (C o.1 : ℝ) S') ∧
      ∃ p : {p // p ∈ protocols o.1},
        Serves (maintained o.1) (sufficient o.1) (usesToRealize o.1) p o.2.carried ∧
        ∃ x : Raw o.1, Cont o.1 x p.val := by sorry
