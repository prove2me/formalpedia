-- Prove2me | Theorems.Thm_APFB06_occupant_jointly_held_of_binding
-- name    : APFB06.occupant_jointly_held_of_binding
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:58:01.272202+00:00
-- url     : https://prove2.me/theorems/cf0063ba-4c58-455e-94f8-3a35cd4d26ab
-- title:
--   Occupant jointly held of binding
-- statement:
--   B06, the empty-word budget condition and a binding of both marks to carried tasks at every actual occupant imply joint holdability at some raw input.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APF_B06_DeclaredInput

set_option autoImplicit false
open APFPaper1.Continuation

theorem APFB06.occupant_jointly_held_of_binding
    {Context : Type*} {Frag : Context → Context → Type*} {Raw : Context → Type*} {R : Context → Type*} {M : Type*}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont step resource calibration C g) → Bool))
    (protocols : (g : Context) → Set (WordFrom Frag g))
    (J : (g : Context) → Finset (APFB06.Task (Cont step resource calibration C g) (D g)) →
      Set {p // p ∈ protocols g})
    (actualJoint :
      Set (Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g)))
    (reads : (h : Context) → Raw h → M → Bool) (m1 m2 : M)
    (hB06 : APFB06.AmendedB06_20260914 (Cont step resource calibration C) D protocols J
      (fun g p => resource g p.val) calibration C actualJoint)
    (hnull : ∀ g : Context, calibration g (resource g (nullWord g)) ≤ C g)
    (hbind : ∀ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint → ∃ d1 ∈ o.2.carried, ∃ d2 ∈ o.2.carried,
        (∀ y : Raw o.1,
          reads o.1 y m1 = d1.val (APFB01.physicalClass (Cont step resource calibration C o.1) y)) ∧
        (∀ y : Raw o.1,
          reads o.1 y m2 = d2.val (APFB01.physicalClass (Cont step resource calibration C o.1) y))) :
    ∃ (g : Context) (x : Raw g),
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by sorry
