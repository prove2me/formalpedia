-- Prove2me | Theorems.Thm_AKNMixed_FQP_embedOn_comm
-- name    : AKNMixed.FQP.embedOn_comm
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:00.627888+00:00
-- url     : https://prove2.me/theorems/39ce2b39-7c05-42f4-8184-357708116d47
-- title:
--   Lemma 3 — gates on different qubits commute
-- statement:
--   Let $T_1$ be a linear super-operator on $k_1$ qubits and $T_2$ a linear super-operator on $k_2$ qubits, placed on wire lists $w_1$ and $w_2$ of an $N$-qubit system with no wire in common, and extended by the identity to the whole system. Then, for every $N$-qubit matrix $\rho$,
--
--   $$T_1\circ T_2\circ\rho=T_2\circ T_1\circ\rho .$$
--
--   Together with the encoding of a node as such an extension, this is the reason the final density matrix of a circuit does not depend on the topological sort (Lemma 2).
--
--   Differences from the source:
--   - generalization: g1, g2 quantum gates → T₁, T₂ any ℂ-linear super-operators; reason: every quantum gate is linear (Definition 1); the Lean statement specializes to gates
--   - encoding: gates operating on different qubits, extended by tensoring with the identity → embedOn w₁ T₁ and embedOn w₂ T₂ for wire lists with disjoint ranges, each map square on its wires; reason: a node of order (k, l) acts as a square map on its k + l input and output wires (wire-pool encoding of the circuit)
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 3, p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_embedOn

namespace AKNMixed.FQP

open QAlgorithms

/-- **Lemma 3: gates operating on different qubits commute.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 3, p. 8: "Let g1, g2 be two quantum gates operating on different qubits. Then ∀ ρ,
g1 ∘ g2 ∘ ρ = g2 ∘ g1 ∘ ρ."

For linear super-operators `T₁` on `k₁` qubits and `T₂` on `k₂` qubits, placed on wire lists
`w₁`, `w₂` of an `N`-wire system with no wire in common, the extensions by the identity commute:
`embedOn w₁ T₁ ∘ embedOn w₂ T₂ = embedOn w₂ T₂ ∘ embedOn w₁ T₁` on every `N`-qubit matrix.

**Formalization Note.** Linearity replaces "quantum gate" (a generalization: every gate is
linear). A gate acts on the whole system through its extension `embedOn` (p. 8, "we tensor with
the identity"); in the wire-pool encoding a node's step (`Node.step`) is such an extension on the
node's input and output wires. -/
theorem embedOn_comm {N k₁ k₂ : ℕ} (w₁ : Fin k₁ ↪ Fin N) (w₂ : Fin k₂ ↪ Fin N)
    (hw : Disjoint (Set.range w₁) (Set.range w₂))
    (T₁ : Superop (Qubits k₁) (Qubits k₁)) (T₂ : Superop (Qubits k₂) (Qubits k₂))
    (h₁ : IsLinearMap ℂ T₁) (h₂ : IsLinearMap ℂ T₂) :
    embedOn w₁ T₁ ∘ embedOn w₂ T₂ = embedOn w₂ T₂ ∘ embedOn w₁ T₁ := by sorry

end AKNMixed.FQP
