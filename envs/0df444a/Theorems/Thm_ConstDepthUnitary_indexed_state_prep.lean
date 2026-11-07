-- Prove2me | Theorems.Thm_ConstDepthUnitary_indexed_state_prep
-- name    : ConstDepthUnitary.indexed_state_prep
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:30.979462+00:00
-- url     : https://prove2.me/theorems/88ae1de9-57ce-4b75-85a1-fdd515a67e66
-- title:
--   Lemma 6.5 — indexed state preparation in constant depth
-- statement:
--   There are universal constants $d_0,C,c$ such that for all $r$ and $s\ge1$ and any $r$-qubit states $|\psi_0\rangle,\dots,|\psi_{s-1}\rangle$ there is a circuit $D$ with fan-out, of depth at most $d_0$, with at most $Cg(\log_2(g+2))^c$ ancillas, $g=s2^r$, such that
--   $$D|j\rangle|0^r\rangle|0,\dots,0\rangle=|j\rangle|\psi_j\rangle|0,\dots,0\rangle\qquad(j=0,\dots,s-1).$$
--
--   The paper cites this result from Rosenthal (2021). The index register has $\lceil\log_2s\rceil$ qubits and holds $j$ most significant bit first.
--
--   Differences from the source:
--   - reading: Õ(s 2^r) → C·g·(log₂(g + 2))^c with g = s 2^r and universal C, c; reason: the paper does not define Õ; this is g·polylog(g), not zero at small g
--   - encoding: |j⟩ on an unspecified register, a vector identity → a register of ⌈log₂ s⌉ qubits, big-endian, and the identity amplitude by amplitude; reason: the same identity on the same inputs
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.5, p.36

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ConstDepthUnitary

/-- Lemma 6.5 (indexed state preparation, [Ros21]): for any `r`-qubit states `|ψ₀⟩, …, |ψ_{s−1}⟩` there is a circuit `C` with
fan-out, of universally bounded depth with `Õ(s 2^r)` ancillas, such that `C |j⟩ |0^r⟩ |0, …, 0⟩ = |j⟩ |ψ_j⟩ |0, …, 0⟩`
for all `j ∈ {0, …, s − 1}`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.5, p.36.

**Formalization Note** The index register has `⌈log₂ s⌉` qubits and holds `j` big-endian (`QAlgorithms.natToBits`). Only the
listed inputs are constrained. The output is stated amplitude by amplitude: on the basis state `y`, `C` applied to
`|j⟩|0^r⟩|0⟩` has the amplitude `ψ_j(y|_r)` if `y` holds `j` and zero ancillas, and `0` otherwise. -/
theorem indexed_state_prep :
    ∃ (d₀ : ℕ) (C : ℝ) (c : ℕ), ∀ (r s : ℕ), 0 < s → ∀ ψ : Fin s → (Fin r → Bool) → ℂ,
      (∀ j, ∑ x, ‖ψ j x‖ ^ 2 = 1) →
      ∃ (m : ℕ) (D : Circuit ((Fin (Nat.clog 2 s) ⊕ Fin r) ⊕ Fin m)),
        (m : ℝ) ≤ C * ((s : ℝ) * 2 ^ r) * Real.logb 2 ((s : ℝ) * 2 ^ r + 2) ^ c ∧
        D.depth ≤ d₀ ∧
        ∀ (j : Fin s) (y : (Fin (Nat.clog 2 s) ⊕ Fin r) ⊕ Fin m → Bool),
          D.matrix.mulVec
              (Pi.single (Sum.elim (Sum.elim (QAlgorithms.natToBits _ j) fun _ => false) fun _ => false) 1) y =
            if (fun i => y (Sum.inl (Sum.inl i))) = QAlgorithms.natToBits _ j ∧ ∀ a, y (Sum.inr a) = false then
              ψ j fun i => y (Sum.inl (Sum.inr i))
            else 0 := by sorry

end ConstDepthUnitary
