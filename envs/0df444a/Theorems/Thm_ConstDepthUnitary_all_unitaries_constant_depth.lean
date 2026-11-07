-- Prove2me | Theorems.Thm_ConstDepthUnitary_all_unitaries_constant_depth
-- name    : ConstDepthUnitary.all_unitaries_constant_depth
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:50:12.716041+00:00
-- url     : https://prove2.me/theorems/f7c3b4c8-d425-476e-86c8-441047c14fb7
-- title:
--   Corollary 7.2 — every unitary has an exact constant-depth circuit with fan-out and an exact depth-$O(n)$ circuit
-- statement:
--   There are universal constants $d_0,C,c$ such that for all $n$ and every $n$-qubit unitary $U$:
--
--   1. there is a circuit $D$ of one-qubit, two-qubit and fan-out gates of depth at most $d_0$, with $m\le2^{c(n+1)}$ ancillas, such that
--   $$D\,(I\otimes|0^m\rangle)=(I\otimes|0^m\rangle)\,U;$$
--   2. there is a circuit $D$ of one- and two-qubit gates only, of depth at most $C(n+1)$, with $m\le2^{c(n+1)}$ ancillas and the same exact identity.
--
--   The depth does not depend on $n$ or $U$ in the first clause, and it is linear in $n$ in the second.
--
--   Differences from the source:
--   - reading: "a clean, exact implementation in QACf with 2^O(n) ancilla qubits", naming no depth → depth at most a universal constant d₀; reason: Theorem 1.1, the title and the proof ("an exact constant-depth QACf circuit") give the depth; it is the stronger reading
--   - encoding: 2^O(n), O(n) → 2^(c(n+1)), C(n+1); reason: at n = 0 a global phase needs a gate on an ancilla; for n ≥ 1 these are at most 2^(2cn), 2Cn
--   - encoding: "clean, exact" → D(I ⊗ |0⟩) = (I ⊗ |0⟩)U; reason: it implies the block identity of Theorem 7.1 and is equivalent to it for unitary U
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 7.2, p.43; Theorem 1.1, p.3

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_CleanlyImplements

namespace ConstDepthUnitary

/-- Corollary 7.2 (the formal form of the headline Theorem 1.1): every `n`-qubit unitary has a clean, exact implementation
with fan-out, of depth at most a universal constant, with `2^{O(n)}` ancilla qubits; consequently every unitary is implemented
exactly in depth `O(n)` by one- and two-qubit gates with `2^{O(n)}` ancilla qubits.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 7.2, p.43; Theorem 1.1, p.3.

**Formalization Note** The constant depth of the first clause is the reading of Theorem 1.1, of the title and of the
corollary's proof ("an exact constant-depth QACf circuit"). Bounds use `n + 1`: at `n = 0` a global phase needs a gate on an
ancilla. Fan-outs act on at most `n + m` qubits, so they have size `2^{O(n)}` automatically. -/
theorem all_unitaries_constant_depth :
    (∃ d₀ c : ℕ, ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n → Bool) ℂ),
      ∃ (m : ℕ) (D : Circuit (Fin n ⊕ Fin m)),
        m ≤ 2 ^ (c * (n + 1)) ∧ D.depth ≤ d₀ ∧
        CleanlyImplements D (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) ∧
    (∃ C c : ℕ, ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n → Bool) ℂ),
      ∃ (m : ℕ) (D : Circuit (Fin n ⊕ Fin m)),
        m ≤ 2 ^ (c * (n + 1)) ∧ D.IsStandard ∧ D.depth ≤ C * (n + 1) ∧
        CleanlyImplements D (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by sorry

end ConstDepthUnitary
