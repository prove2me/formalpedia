-- Prove2me | Theorems.Thm_APFB06_amendedB06_extract_E
-- name    : APFB06.amendedB06_extract_E
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T15:24:59.624731+00:00
-- url     : https://prove2.me/theorems/6ea08974-6435-4392-8d2d-013108725128
-- title:
--   The amended occupancy input supplies one occupied family, one joint protocol and one input from which it is available
-- statement:
--   ### What this establishes
--
--   Assume the amended **B06 occupancy input**. There is an actual alignment with a nonempty carried family, a protocol in that family's original joint class, and a raw input from which that same complete protocol is available.
--
--   The accompanying checked lemmas retain the held-family cost bound and show that a finite bound on an extended-real joint-cost infimum forces the joint class to be nonempty.
--
--   ### Scope
--
--   The continuation profile remains a parameter. The theorem does not bound the selected protocol's bill by capacity, identify its input with the alignment's carrier, or assert observed execution. Availability comes from the adopted B06 clause, not from the infimal cost bound.
--
--   **Foundation Inputs:** revision 2026-10-04.1. **Input consumed:** B06; existing B01 vocabulary supplies the carrier quotient. No new definition or physical premise is added.
-- source:
--   Paper 1 Technical Supplement v9.28, 1872–1884 (amended occupancy), 1831–1845 (structural alignment); FOUNDATION_INPUTS.json revision 2026-10-04.1. Source module Theorems.Thm_APFB06_amended_occupancy_extraction; SHA256 a5f15cd30b467c79f4061b8c55ab2f3b3e3b22de74932665c7a283ff1fa1557d.

import Definitions.Def_APF_B06_DeclaredInput
set_option autoImplicit false

open APFB06

theorem APFB06.amendedB06_extract_E
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val := by sorry
