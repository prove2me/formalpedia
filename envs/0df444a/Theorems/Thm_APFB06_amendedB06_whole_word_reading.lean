-- Prove2me | Theorems.Thm_APFB06_amendedB06_whole_word_reading
-- name    : APFB06.amendedB06_whole_word_reading
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:01:50.979182+00:00
-- url     : https://prove2.me/theorems/86c4a432-8cfa-4590-a5a1-261d231c4c54
-- title:
--   The whole-word reading of B06 supplies an executing budgeted joint protocol
-- statement:
--   B06 is the designated amended occupancy predicate on the shared B01 quotient, original joint protocol class and whole-resource accounting. It supplies one actual alignment with nonempty carried family, its infimal held-cost bound, and a same-whole joint protocol admitted as a continuation from some raw input. The bill bound and execution are input content unpacked through the definition, not a new physical derivation or an author-input amendment. Instantiate B06 with processes equal to typed words, continuation membership equal to whole-word execution within budget, and protocol resource equal to the resource of that same word. There exists an actual alignment with nonempty carried family and a protocol in its joint class whose whole-word bill fits the starting-context capacity and which executes from some raw input to some endpoint. Source: FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.
-- source:
--   Theorems/Thm_APFB06_amendedB06_whole_word_reading.lean, declaration at line 33 (Sib v15; source-scoped review). FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.

import Definitions.Def_APFPaper1_ContinuationWords
import Definitions.Def_APF_B06_DeclaredInput

set_option autoImplicit false
open APFPaper1.Continuation

theorem APFB06.amendedB06_whole_word_reading
    {Context : Type*} {Frag : Context → Context → Type*} {Raw R : Context → Type*}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont step resource calibration C g) → Bool))
    (protocols : (g : Context) → Set (WordFrom Frag g))
    (J : (g : Context) → Finset (APFB06.Task (Cont step resource calibration C g) (D g)) →
      Set {p // p ∈ protocols g})
    (actualJoint :
      Set (Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g)))
    (hB06 : APFB06.AmendedB06_20260914 (Cont step resource calibration C) D protocols J
      (fun g p => resource g p.val) calibration C actualJoint) :
    ∃ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      ∃ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried ∧
        calibration o.1 (resource o.1 p.val) ≤ C o.1 ∧
        ∃ x : Raw o.1, ∃ y : Raw p.val.1, Executes step p.val.2 x y := by sorry
