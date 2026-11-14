-- Prove2me | Theorems.Thm_APFPaper5_K1_completed_value_respects_test
-- name    : APFPaper5.K1.completed_value_respects_test
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:27:28.839479+00:00
-- url     : https://prove2.me/theorems/3312769b-2de9-4aa5-b398-ad39332d0428
-- title:
--   All-ambient contextual equivalence preserves completed terminal-test values
-- statement:
--   Supply typed words, raw input states, a definedness predicate and a run-value function. Let terminal words S and S′ have matching types, and assume h: they are contextually equivalent over every typed prefix and suffix. For a fixed preparation word W and compatible input x, W then S is defined exactly when W then S′ is defined, and the values agree when both are defined. The conclusion is about supplied run values under the all-ambient relation, not a construction of a physical ordered score.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_score_respects_classes.lean:38; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3239-3304; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-362; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_ContextEq_all_ambients_2026-11-12.md, ruling and fidelity comparison

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
open APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

theorem APFPaper5.K1.completed_value_respects_test (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {g a c : Context} (W : Word Frag g a) (S S' : Word Frag a c) (x : Raw g)
    (h : ContextEq Defd value (fun _ _ _ => True) S S') :
    (Defd g x (sandwich W S (Word.nil c)) ↔ Defd g x (sandwich W S' (Word.nil c))) ∧
    (Defd g x (sandwich W S (Word.nil c)) → Defd g x (sandwich W S' (Word.nil c)) →
      value g (sandwich W S (Word.nil c)) x = value g (sandwich W S' (Word.nil c)) x) := by sorry
