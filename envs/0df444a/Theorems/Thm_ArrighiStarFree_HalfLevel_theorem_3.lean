-- Prove2me | Theorems.Thm_ArrighiStarFree_HalfLevel_theorem_3
-- name    : ArrighiStarFree.HalfLevel.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:07:30.741201+00:00
-- url     : https://prove2.me/theorems/3b99bd6c-3e8e-44b0-9dea-8977db8f4bb7
-- title:
--   Theorem 3 — logspace completeness at the first half-level
-- statement:
--   For finite automata promised to accept languages in the first half-level of the Straubing–Thérien hierarchy, let $I_N$ be intersection nonemptiness for NFA input, $I_N^1$ its restriction to a one-letter alphabet, and $I_D$ the version with complete DFA input. Then
--   $$I_N\text{ is NL-complete},\qquad I_N^1\text{ is NL-hard},\qquad I_D\text{ is L-complete}.$$
--   Completeness includes both machine class membership and hardness for every binary language in that class. Hardness is under DLOGTIME-uniform AC⁰ many-one reductions, and under ordinary deterministic logspace many-one reductions as well. Reductions always output legal promised instances and preserve both answers.
--
--   This is the full goal of the selected logspace section. The alphabet, list length and all state counts vary with the input, the empty word is permitted, and the promise concerns accepted languages rather than a special shape of automaton.
--
--   Differences from the source:
--   - encoding: finite automata over a common finite alphabet, given as a nonempty list → variable finite indices, unary size and initial-index delimiters, final-state bit vectors and dense transition tables; reason: every finite instance is represented, with input length measured on the complete list encoding
--   - encoding: the accepted languages are promised to belong to the first half-level → a domain of legal encodings and a separate answer predicate; correctness is required only on the domain; reason: the semantic promise is not a recognition task and no witness is included in the input
--   - encoding: deterministic or nondeterministic logarithmic-space Turing machines → one finite multitape binary-choice machine and one positive constant c before all strings, with at most c floor(log₂(n+2)) visited work cells on every branch and halting on all strings; reason: the standard total space-bounded model handles n=0 and charges blank visited cells as well as written cells
--   - reading: weak reductions in Theorem 3 and Lemma 4, AC⁰ reductions in the introduction, and the logspace default in §2 → DLOGTIME-uniform AC⁰ many-one hardness, using the bounded-alternation logarithmic-time random-access model of §2, and ordinary logspace hardness as a separate conjunct; reason: this fixes the weak-reduction convention without replacing it by unrestricted or merely logspace reducibility
--   - encoding: many-one reduction maps on finite input strings → uniform AC⁰ maps specified by a polynomially padded validity/data bit graph, and logspace maps by explicit write-only-output transducers; reason: a validity prefix represents variable output lengths; all source YES and NO strings must map into the legal target domain
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), Theorem 3, printed p. 23:6, PDF p. 6

import Definitions.Def_ArrighiStarFree_HalfLevel_Intersection

namespace ArrighiStarFree.HalfLevel

theorem theorem_3 :
    NLComplete (intersectionProblem false false) ∧
    NLHard (intersectionProblem false true) ∧
    LComplete (intersectionProblem true false) := by sorry

end ArrighiStarFree.HalfLevel
