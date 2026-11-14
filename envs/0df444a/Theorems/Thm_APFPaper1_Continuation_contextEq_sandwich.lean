-- Prove2me | Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich
-- name    : APFPaper1.Continuation.contextEq_sandwich
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:45:29.11994+00:00
-- url     : https://prove2.me/theorems/a76f5c35-f400-4f63-96b9-d23f4245e0e2
-- title:
--   Ambient heredity makes contextual equivalence a strong congruence
-- statement:
--   Two words of the same type are contextually equivalent when every permitted typed prefix and suffix gives the same definedness and, where defined, exactly equal supplied values at each raw input. Definedness, values and the ambient class are parameters of this relation. This is conditional on heredity; it does not derive that law for arbitrary budgeted resources or the Supplement's admissible ambients. Assume ambient heredity: whenever a complete sandwich is defined at a raw input, its outer words belong to the ambient class. If W and W′ are contextually equivalent, then placing any matching typed words L and R before and after them produces contextually equivalent composites. The same definedness, values and ambient predicate are used throughout. Source: Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.
-- source:
--   Theorems/Thm_APFPaper1_ContextualEquivalence_congruence.lean, declaration at line 63 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

theorem APFPaper1.Continuation.contextEq_sandwich (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    (hher : AmbientHeredity Defd Amb)
    {a' a b b' : Context} (Lw : Word Frag a' a) (Rw : Word Frag b b') (W W' : Word Frag a b)
    (hW : ContextEq Defd value Amb W W') :
    ContextEq Defd value Amb (Lw.append (W.append Rw)) (Lw.append (W'.append Rw)) := by sorry
