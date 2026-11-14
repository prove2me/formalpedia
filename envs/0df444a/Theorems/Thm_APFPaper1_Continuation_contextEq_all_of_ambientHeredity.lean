-- Prove2me | Theorems.Thm_APFPaper1_Continuation_contextEq_all_of_ambientHeredity
-- name    : APFPaper1.Continuation.contextEq_all_of_ambientHeredity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:48:55.146852+00:00
-- url     : https://prove2.me/theorems/093fc49e-cf3a-4a08-8e84-608f7a6d6392
-- title:
--   Ambient heredity extends restricted equivalence to all words
-- statement:
--   Two words of the same type are contextually equivalent when every permitted typed prefix and suffix gives the same definedness and, where defined, exactly equal supplied values at each raw input. Definedness, values and the ambient class are parameters of this relation. Heredity is retained as an explicit premise. This direction alone does not assert that a physical continuation model has heredity, and it supplies no physical identification of the value function. Assume ambient heredity for supplied definedness and ambient class. If W and W′ are contextually equivalent using that class, then they are contextually equivalent when all typed words are allowed as ambients. A defined composite supplies the ambient memberships needed to invoke the restricted relation on either side. Source: Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.
-- source:
--   Theorems/Thm_APFPaper1_ContextualEquivalence_congruence.lean, declaration at line 112 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3239–3250; November 12 all-ambient contextual-equivalence ruling.

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

theorem APFPaper1.Continuation.contextEq_all_of_ambientHeredity (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    (hher : AmbientHeredity Defd Amb) {a b : Context} (W W' : Word Frag a b)
    (h : ContextEq Defd value Amb W W') : ContextEq Defd value (fun _ _ _ => True) W W' := by sorry
