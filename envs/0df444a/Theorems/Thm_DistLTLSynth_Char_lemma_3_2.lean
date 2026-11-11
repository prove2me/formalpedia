-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_2
-- name    : DistLTLSynth.Char.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:42.859643+00:00
-- url     : https://prove2.me/theorems/2264fcb6-e01b-45ca-a15b-8484840f8398
-- title:
--   Lemma 3.2 — repeated bounded-time consensus iff π(A) is nowhere dense; uniform bound for ω-regular A
-- statement:
--   Fix a finite proposal set $V$ with $|V|\ge2$. For every message adversary $A$: consensus is repeatedly solvable in bounded time under $A$ (solvable in bounded time under every left quotient $h^{-1}A$, $h\in\mathrm{Pref}(A)$) if and only if $\pi(A)$ is nowhere dense,
--   $$\forall h\in\mathrm{Pref}(A):\ \text{bounded-time consensus under } h^{-1}A\iff \big(\overline{\pi(A)}\big)^\circ=\emptyset .$$
--   In this case, if $A$ is ω-regular, consensus is repeatedly solvable in uniformly bounded time (one bound $R$ for all $h$). It links the decidability boundary to consensus.
--
--   Differences from the source:
--   - encoding: A is ω-regular (given by a parity automaton) → A is the language of a deterministic parity automaton with a finite state type (least priority seen infinitely often is even); reason: the paper's own standing assumption (§1.1, §3.3, Def. 7.6); deterministic parity automata recognize exactly the ω-regular languages
--   - encoding: π(A) nowhere dense in [0, 1] → IsNowhereDense (piMap '' A) in ℝ; reason: π(A) ⊆ [0, 1] and [0, 1] is closed in ℝ, so nowhere density in the subspace and in ℝ coincide
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
--   - reading: (1) all non-⊥ outputs are irrevocable → irrevocability is required in every execution whose graph history is in A (the executions considered for solvability); reason: §5.1 quantifies the bounded-time clause over 'all executions considered for solvability'; the two readings give the same solvability notion (a process can latch its first decision, which is in its view)
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 8 (PDF 9), Lemma 3.2

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus

namespace DistLTLSynth.Char

/-- Lemma 3.2: consensus is repeatedly solvable in bounded time under `A` iff `π(A)` is
nowhere dense; in this case, if `A` is ω-regular, consensus is repeatedly solvable in
uniformly bounded time. -/
theorem lemma_3_2 (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    (RepeatedlySolvableBounded V A ↔ IsNowhereDense (piMap '' A)) ∧
      (IsNowhereDense (piMap '' A) →
        ∀ (S : Type) [Fintype S] (M : DPA S CommGraph), M.lang = A →
          RepeatedlySolvableUniform V A) := by sorry

end DistLTLSynth.Char
