-- Prove2me | Theorems.Thm_AKNMixed_FQP_marginal_embedOn_of_disjoint
-- name    : AKNMixed.FQP.marginal_embedOn_of_disjoint
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:08.666298+00:00
-- url     : https://prove2.me/theorems/266feec4-58dc-43e7-801f-faf8378bd9f0
-- title:
--   Lemma 7 — a gate off $B$ leaves the reduced state on $B$ unchanged
-- statement:
--   Let $T$ be a linear, trace-preserving super-operator acting on a list $w$ of wires of an $N$-qubit system, and let $B$ be a list of wires disjoint from $w$. Then for every $N$-qubit matrix $\rho$
--
--   $$\rho|_B=(T\circ\rho)|_B ,$$
--
--   where $T$ acts on the whole system through its extension by the identity.
--
--   In the proof of Theorem 2 this is what allows garbage and ancilla qubits to be acted on and then discarded without changing the state of the original qubits.
--
--   Differences from the source:
--   - generalization: g a gate → T any ℂ-linear, trace-preserving super-operator; reason: every gate is linear and trace preserving (Definition 1); the Lean statement specializes to gates
--   - encoding: a gate operating on qubits not in B → embedOn w T with the range of w disjoint from the range of B, T square on its wires; reason: a node of order (k, l) acts as a square map on its k + l wires (wire-pool encoding)
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 7, p. 13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_embedOn
import Definitions.Def_AKNMixed_FQP_marginal

namespace AKNMixed.FQP

open QAlgorithms

/-- **Lemma 7: a gate acting outside `B` does not change the reduced density matrix on `B`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 7, p. 13: "Let g be a gate operating on qubits not in the set B. ρ|B = (g ∘ ρ)|B."

Let `w` and `B` be wire lists of an `N`-wire system with no wire in common, and let `T` be a
linear, trace-preserving super-operator on the `k` wires of `w`. Then for every `N`-qubit
matrix `ρ`, the reduced matrix on `B` is unchanged: `(embedOn w T ρ)|_B = ρ|_B`.

**Formalization Note.** Linear and trace preserving replace "gate" (a generalization: every gate
has both properties). The gate acts on the whole system through `embedOn` (tensor with the
identity, p. 6 and p. 8). -/
theorem marginal_embedOn_of_disjoint {N k b : ℕ} (w : Fin k ↪ Fin N) (B : Fin b ↪ Fin N)
    (hwB : Disjoint (Set.range w) (Set.range B)) (T : Superop (Qubits k) (Qubits k))
    (hlin : IsLinearMap ℂ T) (htr : ∀ X : Matrix (Qubits k) (Qubits k) ℂ, (T X).trace = X.trace)
    (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    marginal B (embedOn w T ρ) = marginal B ρ := by sorry

end AKNMixed.FQP
