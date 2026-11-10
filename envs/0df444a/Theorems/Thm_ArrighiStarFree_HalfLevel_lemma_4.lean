-- Prove2me | Theorems.Thm_ArrighiStarFree_HalfLevel_lemma_4
-- name    : ArrighiStarFree.HalfLevel.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:07:28.650434+00:00
-- url     : https://prove2.me/theorems/7709e815-199a-47d3-84da-ddc955330547
-- title:
--   Lemma 4 — unary NFA NL-hardness and unary DFA L-hardness
-- statement:
--   Consider intersection nonemptiness for a nonempty finite list of automata over a one-letter alphabet, promised to accept languages in the first half-level of the Straubing–Thérien hierarchy. Write $I_N^1$ for NFA input and $I_D^1$ for complete DFA input. Then
--   $$I_N^1\text{ is NL-hard},\qquad I_D^1\text{ is L-hard}.$$
--   Both hardness assertions use uniform AC⁰ many-one reductions and also retain the ordinary deterministic logspace convention. Every language in the relevant class reduces to the corresponding promise problem, with both YES and NO inputs mapped into its legal domain.
--
--   This is the lower-bound milestone for Theorem 3. No bound is placed on the number of input automata or states.
--
--   Differences from the source:
--   - encoding: finite automata over a common finite alphabet, given as a nonempty list → variable finite indices, unary size and initial-index delimiters, final-state bit vectors and dense transition tables; reason: every finite instance is represented, with input length measured on the complete list encoding
--   - encoding: the accepted languages are promised to belong to the first half-level → a domain of legal encodings and a separate answer predicate; correctness is required only on the domain; reason: the semantic promise is not a recognition task and no witness is included in the input
--   - encoding: deterministic or nondeterministic logarithmic-space Turing machines → one finite multitape binary-choice machine and one positive constant c before all strings, with at most c floor(log₂(n+2)) visited work cells on every branch and halting on all strings; reason: the standard total space-bounded model handles n=0 and charges blank visited cells as well as written cells
--   - reading: weak reductions in Theorem 3 and Lemma 4, AC⁰ reductions in the introduction, and the logspace default in §2 → DLOGTIME-uniform AC⁰ many-one hardness, using the bounded-alternation logarithmic-time random-access model of §2, and ordinary logspace hardness as a separate conjunct; reason: this fixes the weak-reduction convention without replacing it by unrestricted or merely logspace reducibility
--   - encoding: many-one reduction maps on finite input strings → uniform AC⁰ maps specified by a polynomially padded validity/data bit graph, and logspace maps by explicit write-only-output transducers; reason: a validity prefix represents variable output lengths; all source YES and NO strings must map into the legal target domain
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), Lemma 4, printed p. 23:6, PDF p. 6

import Definitions.Def_ArrighiStarFree_HalfLevel_Intersection

namespace ArrighiStarFree.HalfLevel

theorem lemma_4 :
    NLHard (intersectionProblem false true) ∧
    LHard (intersectionProblem true true) := by sorry

end ArrighiStarFree.HalfLevel
