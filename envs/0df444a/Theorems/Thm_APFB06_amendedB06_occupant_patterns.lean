-- Prove2me | Theorems.Thm_APFB06_amendedB06_occupant_patterns
-- name    : APFB06.amendedB06_occupant_patterns
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T19:48:13.226319+00:00
-- url     : https://prove2.me/theorems/e4c52dd7-4cfb-481a-aac9-154add8a5ca9
-- title:
--   An occupied family of k two-valued distinctions has at least 1 + log₂(k + 1) joint evaluation patterns
-- statement:
--   ### Joint evaluation patterns of an occupied family
--
--   Assume the amended **B06 occupancy input** and the explicit hypothesis **`hnt`**: each distinction takes both Boolean values on the physical quotient. This quotient-level hypothesis is supplied here; the theorem does not derive it from the raw-input B02 node.
--
--   For the occupied alignment supplied by B06, let:
--
--   - **k** be the number of distinctions in its carried family;
--   - **N** be the number of different joint Boolean answer patterns attained as a quotient state varies.
--
--   Then
--
--   $$k+1\leq 2^{N-1},\qquad N\geq 2.$$
--
--   Equivalently, the pattern count is at least $1+\log_2(k+1)$. The same occupied alignment, available joint protocol and raw input from B06 are retained.
--
--   ### Why the count follows
--
--   The carrier supplies an all-true pattern. On the remaining patterns, the k distinction columns and one extra constant-true column are all different. There are only $2^{N-1}$ Boolean columns on those patterns.
--
--   ### Scope
--
--   These are **joint evaluations of functions**, not a construction of simultaneous physical readout. The theorem supplies no measurement record, prepared state or observed execution. It does not require the entire physical quotient to be finite. Continuation remains a parameter.
--
--   **Premises:** B06 and the named `hnt` condition. Foundation Inputs revision 2026-10-04.1. No definition or input is changed. The proof file includes the finite counting lemma and its arithmetic consequence.
-- source:
--   Paper 1 Technical Supplement v9.28:1744–1751 (quotient-descending distinctions), 1831–1845 (active carried family), 1872–1884 (amended occupancy); FOUNDATION_INPUTS.json revision 2026-10-04.1. Source Theorems.Thm_APFB06_occupant_patterns; SHA256 a0a446cf61b856811984584d827fe9184d0150f004d331cbd61394ee2ac86a4e. Explicit quotient-level two-valuedness hypothesis hnt; no B02-to-quotient bridge is asserted.

import Definitions.Def_APF_B06_DeclaredInput
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.ByContra
set_option autoImplicit false
open APFB06

theorem APFB06.amendedB06_occupant_patterns
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (hnt : ∀ (g : Context) (d : Task (Cont g) (D g)),
      ∃ s t : APFB01.PhysicalState (Cont g), d.val s ≠ d.val t)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      o.2.carried.card + 1 ≤
        2 ^ (Nat.card (Set.range (fun (s : APFB01.PhysicalState (Cont o.1))
          (d : {d // d ∈ o.2.carried}) => d.val.val s)) - 1) ∧
      2 ≤ Nat.card (Set.range (fun (s : APFB01.PhysicalState (Cont o.1))
          (d : {d // d ∈ o.2.carried}) => d.val.val s)) := by sorry
