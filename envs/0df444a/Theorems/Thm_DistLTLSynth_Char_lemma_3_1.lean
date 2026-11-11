-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_1
-- name    : DistLTLSynth.Char.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:50.459346+00:00
-- url     : https://prove2.me/theorems/27e17ff4-7a29-4dfd-8456-3bece275f140
-- title:
--   Lemma 3.1 ([CG23, Thm 26]) — consensus is solvable under A iff π(A) ≠ [0, 1]
-- statement:
--   Fix a finite proposal set $V$ with $|V|\ge2$. For every message adversary $A\subseteq\Gamma^\omega$,
--   $$\text{consensus is solvable under } A\iff \pi(A)\neq[0,1].$$
--   This cited characterization (Coutouly–Godard) is the base case of the paper's consensus analysis.
--
--   Differences from the source:
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
--   - reading: (1) all non-⊥ outputs are irrevocable → irrevocability is required in every execution whose graph history is in A (the executions considered for solvability); reason: §5.1 quantifies the bounded-time clause over 'all executions considered for solvability'; the two readings give the same solvability notion (a process can latch its first decision, which is in its view)
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 8 (PDF 9), Lemma 3.1

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Consensus

namespace DistLTLSynth.Char

/-- Lemma 3.1 ([CG23, Theorem 26]): for a finite proposal set `V` with `|V| ≥ 2`, consensus is
solvable under `A` iff `π(A) ≠ [0, 1]`. -/
theorem lemma_3_1 (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    ConsensusSolvable V A ↔ piMap '' A ≠ Set.Icc (0 : ℝ) 1 := by sorry

end DistLTLSynth.Char
