-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_5_2
-- name    : DistLTLSynth.Char.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:53.375632+00:00
-- url     : https://prove2.me/theorems/171b299e-f3b6-40a1-bbef-b97ba29e1f56
-- title:
--   Lemma 5.2 — consensus is solvable in bounded time under A iff π(A) is not dense in [0, 1]
-- statement:
--   Fix a finite proposal set $V$ with $|V|\ge2$. For every message adversary $A$,
--   $$\text{consensus is solvable in bounded time under } A\iff \pi(A)\text{ is not dense in }[0,1],$$
--   i.e. iff $\overline{\pi(A)}\neq[0,1]$. A common decision bound requires a whole interval missing from the image, not just one point.
--
--   Differences from the source:
--   - encoding: π(A) is not dense in [0, 1] → closure (piMap '' A) ≠ Set.Icc 0 1 (closure in ℝ); reason: π(A) ⊆ [0, 1] and [0, 1] is closed, so its closure in [0, 1] and in ℝ agree
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
--   - reading: (1) all non-⊥ outputs are irrevocable → irrevocability is required in every execution whose graph history is in A (the executions considered for solvability); reason: §5.1 quantifies the bounded-time clause over 'all executions considered for solvability'; the two readings give the same solvability notion (a process can latch its first decision, which is in its view)
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 17 (PDF 18), Lemma 5.2

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Consensus

namespace DistLTLSynth.Char

/-- Lemma 5.2: consensus is solvable in bounded time under `A` iff `π(A)` is not dense in
`[0, 1]`, i.e. iff the closure of `π(A) ⊆ [0, 1]` is not all of `[0, 1]`. -/
theorem lemma_5_2 (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    ConsensusSolvableBounded V A ↔ closure (piMap '' A) ≠ Set.Icc (0 : ℝ) 1 := by sorry

end DistLTLSynth.Char
