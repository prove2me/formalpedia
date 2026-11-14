-- Prove2me | Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich_all
-- name    : APFPaper1.Continuation.contextEq_sandwich_all
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:47:03.175626+00:00
-- url     : https://prove2.me/theorems/6b08dd88-a28a-41f6-9aef-6f54f06b2cf9
-- title:
--   All-word contextual equivalence is a strong congruence
-- statement:
--   Two words of the same type are contextually equivalent when every permitted typed prefix and suffix gives the same definedness and, where defined, exactly equal supplied values at each raw input. Definedness, values and the ambient class are parameters of this relation. The theorem concerns the author-selected all-word relation on supplied definedness and values. It does not assert unconditional equality with the Supplement's relation restricted to admissible ambient words, or construct the physical value assignment. Take every typed word as an allowed ambient prefix or suffix. If words W and W′ are contextually equivalent, placing any matching typed words L and R around them yields contextually equivalent composites. No ambient-heredity hypothesis is needed for this all-word relation: the ambient predicate is constantly true. Source: Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.
-- source:
--   Theorems/Thm_APFPaper1_ContextualEquivalence_congruence.lean, declaration at line 81 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

theorem APFPaper1.Continuation.contextEq_sandwich_all (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a' a b b' : Context} (Lw : Word Frag a' a) (Rw : Word Frag b b') (W W' : Word Frag a b)
    (hW : ContextEq Defd value (fun _ _ _ => True) W W') :
    ContextEq Defd value (fun _ _ _ => True) (Lw.append (W.append Rw)) (Lw.append (W'.append Rw)) := by sorry
