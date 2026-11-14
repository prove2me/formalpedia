-- Prove2me | Theorems.Thm_APFB06_occupant_jointly_held
-- name    : APFB06.occupant_jointly_held
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:14:35.1024+00:00
-- url     : https://prove2.me/theorems/ea53701b-c92d-4cc6-ae4a-f95c84e174d9
-- title:
--   B06 and an endpoint bridge yield a jointly saved pair
-- statement:
--   B06 is the designated amended occupancy predicate on the shared B01 quotient, original joint protocol class and whole-resource accounting. It supplies one actual alignment with nonempty carried family, its infimal held-cost bound, and a same-whole joint protocol admitted as a continuation from some raw input. The universal endpoint bridge and raw-state readings are additional supplied data. This does not produce a disturbance defeating the pair, an irreducibly-joint regulation obstruction, or a probability. The bridge is not derived from B06 by this theorem. Assume B06 at the corrected whole-word continuation class. Also assume that every protocol in each actual alignment's joint class, whenever it executes from any raw input, ends with the two supplied marks both reading true. Then some context and raw input admit one budgeted response with a run saving both marks. Source: FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.
-- source:
--   Theorems/Thm_APFB06_occupant_regulation.lean, declaration at line 25 (Sib v15; source-scoped review). FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.

import Definitions.Def_APFPaper1_Regulation
import Theorems.Thm_APFB06_amendedB06_whole_word_reading

set_option autoImplicit false
open APFPaper1.Continuation

theorem APFB06.occupant_jointly_held
    {Context : Type*} {Frag : Context → Context → Type*} {Raw R : Context → Type*} {M : Type*}
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
    (hbridge : ∀ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint → ∀ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried →
        ∀ (x : Raw o.1) (y : Raw p.val.1), Executes step p.val.2 x y →
          reads p.val.1 y m1 = true ∧ reads p.val.1 y m2 = true) :
    ∃ (g : Context) (x : Raw g),
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by sorry
