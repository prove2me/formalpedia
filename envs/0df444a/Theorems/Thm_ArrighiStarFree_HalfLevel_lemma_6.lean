-- Prove2me | Theorems.Thm_ArrighiStarFree_HalfLevel_lemma_6
-- name    : ArrighiStarFree.HalfLevel.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:07:30.006213+00:00
-- url     : https://prove2.me/theorems/ff47b7e7-7ac8-46e0-b42a-0e2013a134d3
-- title:
--   Lemma 6 — NL and L upper bounds for promised intersection
-- statement:
--   Let $I_N$ denote intersection nonemptiness for a nonempty finite list of NFAs over an arbitrary common finite alphabet, under the semantic promise that each accepted language belongs to the first half-level. Let $I_D$ be the same problem for complete DFA input. Then
--   $$I_N\in\mathrm{NL},\qquad I_D\in\mathrm L.$$
--   Each assertion supplies one machine and one logarithmic-space constant for all input lengths. The nondeterministic machine accepts a promised YES input on some branch and a promised NO input on no branch. Both machines halt and obey their resource bound on all strings; off-promise outputs are arbitrary.
--
--   This is the upper-bound milestone. The input is the explicit list of automata, without a shortest-word oracle, promise recognizer or product automaton.
--
--   Differences from the source:
--   - encoding: finite automata over a common finite alphabet, given as a nonempty list → variable finite indices, unary size and initial-index delimiters, final-state bit vectors and dense transition tables; reason: every finite instance is represented, with input length measured on the complete list encoding
--   - encoding: the accepted languages are promised to belong to the first half-level → a domain of legal encodings and a separate answer predicate; correctness is required only on the domain; reason: the semantic promise is not a recognition task and no witness is included in the input
--   - encoding: deterministic or nondeterministic logarithmic-space Turing machines → one finite multitape binary-choice machine and one positive constant c before all strings, with at most c floor(log₂(n+2)) visited work cells on every branch and halting on all strings; reason: the standard total space-bounded model handles n=0 and charges blank visited cells as well as written cells
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), Lemma 6, printed p. 23:7, PDF p. 7

import Definitions.Def_ArrighiStarFree_HalfLevel_Intersection

namespace ArrighiStarFree.HalfLevel

theorem lemma_6 :
    InNL (intersectionProblem false false) ∧
    InL (intersectionProblem true false) := by sorry

end ArrighiStarFree.HalfLevel
