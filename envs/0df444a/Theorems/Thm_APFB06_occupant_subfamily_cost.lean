-- Prove2me | Theorems.Thm_APFB06_occupant_subfamily_cost
-- name    : APFB06.occupant_subfamily_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:17:06.802855+00:00
-- url     : https://prove2.me/theorems/e015401d-6876-4054-9920-50e2879f9e9d
-- title:
--   B06 bounds each occupied subfamily when joint service restricts
-- statement:
--   B06 is the designated amended occupancy predicate on the shared B01 quotient, original joint protocol class and whole-resource accounting. It supplies one actual alignment with nonempty carried family, its infimal held-cost bound, and a same-whole joint protocol admitted as a continuation from some raw input. Downward closure of the supplied joint classes is an explicit premise here; the theorem does not derive it or identify originalCost with a separate real-valued familyCost encoding. No pair-score or probability interpretation follows from finiteness. Assume B06 and that every protocol in the joint class of a family also belongs to the joint class of each subfamily. There exists an actual alignment with nonempty carried family such that every subfamily has extended-nonnegative infimal joint cost at most the context capacity and different from infinity. Source: FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.
-- source:
--   Theorems/Thm_APFB06_occupant_subfamily_cost.lean, declaration at line 22 (Sib v15; source-scoped review). FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.

import Definitions.Def_APF_B06_DeclaredInput
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false

theorem APFB06.occupant_subfamily_cost
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (APFB06.Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => APFB06.OriginalAlignment (Cont g) (D g)))
    (hB06 : APFB06.AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint)
    (hJ : ∀ (g : Context) (S S' : Finset (APFB06.Task (Cont g) (D g))),
      S' ⊆ S → J g S ⊆ J g S') :
    ∃ o : Sigma fun g => APFB06.OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      ∀ S' : Finset (APFB06.Task (Cont o.1) (D o.1)), S' ⊆ o.2.carried →
        APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) S' ≤ (C o.1 : ENNReal) ∧
        APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) S' ≠ ⊤ := by sorry
