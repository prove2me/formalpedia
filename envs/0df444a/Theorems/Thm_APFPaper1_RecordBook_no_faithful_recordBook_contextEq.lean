-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_no_faithful_recordBook_contextEq
-- name    : APFPaper1.RecordBook.no_faithful_recordBook_contextEq
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:19:16.59604+00:00
-- url     : https://prove2.me/theorems/57d2a40a-1230-4e76-8f5f-8b1cd2d4cd72
-- title:
--   Contextually separated triples admit no faithful commuting sharp map
-- statement:
--   The ambient class remains a parameter; it is not silently specialized to all words. The theorem neither proves the assumed contextual separation nor constructs physical readout values. Its total-word multiplicative model captures the algebraic collapse calculation only, and does not by itself exclude all classical process descriptions or encode every component of a finite-tested defender. Supply definedness, a value function and an ambient-word class. If xzx and zxz are not contextually equivalent for those data, no map into a specified commutative semigroup can be multiplicative, sharp at x and z, and equality-faithful to that contextual-equivalence relation. Source: Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.
-- source:
--   Theorems/Thm_APFPaper1_RecordBook_collapse.lean, declaration at line 64 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.

import Definitions.Def_APFPaper1_RecordBook
import Definitions.Def_APFPaper1_ContextualEquivalence
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
open APFPaper1.Continuation

universe uC uF uM uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF}

theorem APFPaper1.RecordBook.no_faithful_recordBook_contextEq {M : Type uM} [CommSemigroup M]
    {Raw : Context → Type uX} {Val : Type uV}
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    {a : Context} {x z : Frag a a}
    (hsep : ¬ ContextEq Defd value Amb (word3 x z x) (word3 z x z)) :
    ¬ ∃ rho : Word Frag a a → M,
        Multiplicative rho ∧ Sharp rho x ∧ Sharp rho z ∧
          Faithful rho (fun v w => ContextEq Defd value Amb v w) := by sorry
