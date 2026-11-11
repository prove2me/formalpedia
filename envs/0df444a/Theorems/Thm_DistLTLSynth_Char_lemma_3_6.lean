-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_6
-- name    : DistLTLSynth.Char.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:49.076962+00:00
-- url     : https://prove2.me/theorems/53adf1fb-0d51-4458-99be-23d56bc9ffd7
-- title:
--   Lemma 3.6 — from A_adv one can compute a uniform consensus bound D ≥ 1
-- statement:
--   Fix a finite proposal set $V$ with $|V|\ge2$. There is a computable function $D$ on codes of deterministic parity automata such that for every automaton $\mathcal A_{\mathrm{adv}}$ recognizing a message adversary $A$ with nowhere-dense image $\pi(A)$,
--   $$D(\mathcal A_{\mathrm{adv}})\ge1\ \text{ and consensus is solvable within } D(\mathcal A_{\mathrm{adv}}) \text{ rounds under } h^{-1}A\ \text{ for every } h\in\mathrm{Pref}(A).$$
--   $D$ is the block length of the decision procedure.
--
--   Differences from the source:
--   - encoding: 'from A_adv, one can compute a D ≥ 1' → ∃ D : DPACode → ℕ, Computable D, correct on every code whose language has nowhere-dense image; reason: Mathlib's computability on finite codes of automata
--   - encoding: π(A) nowhere dense in [0, 1] → IsNowhereDense (piMap '' A) in ℝ; reason: π(A) ⊆ [0, 1] and [0, 1] is closed in ℝ, so nowhere density in the subspace and in ℝ coincide
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
--   - reading: (1) all non-⊥ outputs are irrevocable → irrevocability is required in every execution whose graph history is in A (the executions considered for solvability); reason: §5.1 quantifies the bounded-time clause over 'all executions considered for solvability'; the two readings give the same solvability notion (a process can latch its first decision, which is in its view)
--   - generalization: §3.3.1 (p. 12) assumes A ≠ ∅ before Lemma 3.6 → every code, A = ∅ included; reason: for A = ∅, Pref(A) = ∅ and the claim reduces to D ≥ 1, so the paper's case A ≠ ∅ is an instance
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 12 (PDF 13), Lemma 3.6

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus

namespace DistLTLSynth.Char

/-- Lemma 3.6: from a deterministic parity automaton `A_adv` for `A` with nowhere-dense image
`π(A)`, one can compute a `D ≥ 1` such that consensus is solvable within `D` rounds under
`h⁻¹A` for every `h ∈ Pref(A)`. -/
theorem lemma_3_6 (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) :
    ∃ D : DPACode → ℕ, Computable D ∧
      ∀ c : DPACode, IsNowhereDense (piMap '' c.lang) →
        1 ≤ D c ∧
          ∀ h ∈ Pref c.lang, ConsensusSolvableWithin V (leftQuot h c.lang) (D c) := by sorry

end DistLTLSynth.Char
