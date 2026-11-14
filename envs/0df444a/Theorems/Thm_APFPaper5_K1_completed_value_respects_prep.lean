-- Prove2me | Theorems.Thm_APFPaper5_K1_completed_value_respects_prep
-- name    : APFPaper5.K1.completed_value_respects_prep
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:25:13.500205+00:00
-- url     : https://prove2.me/theorems/d8f9d142-8443-459d-aef7-7ce6d0e638d2
-- title:
--   All-ambient contextual equivalence preserves completed preparation values
-- statement:
--   Supply typed words, raw input states, a definedness predicate and a run-value function. Let W and W′ have the same source and target, and assume h: they are contextually equivalent over every typed prefix and suffix. For any terminal word S and input x, the completed runs W then S and W′ then S are defined at x under exactly the same conditions, and their values agree whenever both are defined. This uses the author-selected all-ambient relation; it does not construct a physical score or identify the supplied values with physical readouts.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_score_respects_classes.lean:28; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3239-3304; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-362; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_ContextEq_all_ambients_2026-11-12.md, ruling and fidelity comparison

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
open APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

theorem APFPaper5.K1.completed_value_respects_prep (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {g a c : Context} (W W' : Word Frag g a) (S : Word Frag a c) (x : Raw g)
    (h : ContextEq Defd value (fun _ _ _ => True) W W') :
    (Defd g x (sandwich (Word.nil g) W S) ↔ Defd g x (sandwich (Word.nil g) W' S)) ∧
    (Defd g x (sandwich (Word.nil g) W S) → Defd g x (sandwich (Word.nil g) W' S) →
      value g (sandwich (Word.nil g) W S) x = value g (sandwich (Word.nil g) W' S) x) := by sorry
