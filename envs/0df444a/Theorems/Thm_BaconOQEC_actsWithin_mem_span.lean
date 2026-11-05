-- Prove2me | Theorems.Thm_BaconOQEC_actsWithin_mem_span
-- name    : BaconOQEC.actsWithin_mem_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:24:37.847587+00:00
-- url     : https://prove2.me/theorems/93e63383-3711-46d7-ae9b-12565aa9f77d
-- title:
--   Digitizing errors: an operator on a set of qubits is a combination of Paulis supported there
-- statement:
--   Let $n\ge1$, let $F$ be a set of qubits of the $n\times n$ lattice, and let $E$ be any operator on the $n^2$ qubits that acts only on the qubits in $F$ ($E = M\otimes I$ with $M$ an arbitrary operator on the qubits of $F$, not necessarily unitary). Then $E$ is a complex linear combination of Pauli operators supported in $F$:
--
--   $$
--   E \in \operatorname{span}_{\mathbb C}\big\{ P(a,b) \;:\; a_{i,j}\ne0 \text{ or } b_{i,j}\ne0 \implies (i,j)\in F \big\}.
--   $$
--
--   This is the "standard argument of digitizing errors" the paper invokes on p.8 to pass from Pauli errors to arbitrary errors on at most $\lfloor (n-1)/2\rfloor$ qubits.
--
--   **Formalization Note** "Acts only on $F$" is the published predicate `QAlgorithms.ActsWithin`. The site $(i,j)$ is wire $i\cdot n + j$, the same bijection used for $P(a,b)$.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - reading: "By the standard arguments of digitizing errors in quantum error correcting codes" → an operator acting within a set F of qubits lies in the ℂ-span of the P(a,b) supported in F; reason: this is the standard digitization fact the sentence invokes; the paper does not state it
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_BaconOQEC_site
import Definitions.Def_BaconOQEC_pauliXZ

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, p.8: "By the standard arguments of digitizing errors in quantum error
correcting codes, we have thus shown how our operator quantum error correcting subsystem code can
correct up to ⌊(n−1)/2⌋ arbitrary single qubit errors." The digitization step this sentence
invokes: every operator `E` on the `n²` lattice qubits that acts only on the qubits of a set `F` is a
complex linear combination of Pauli operators `P(a, b)` supported in `F`.

**Formalization Note.** "Acts only on the qubits of `F`" is the published `QAlgorithms.ActsWithin F E`
(`E = M ⊗ I` with `M` an arbitrary, not necessarily unitary, operator on wires inside `F`). The site
`(i, j)` is the wire `BaconOQEC.site i j` (`finProdFinEquiv`), the same bijection `pauliXZ` uses.
`n = m + 1`. -/
theorem actsWithin_mem_span (m : ℕ) (F : Finset (Fin ((m + 1) * (m + 1))))
    (E : Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ)
    (hE : ActsWithin F E) :
    E ∈ Submodule.span ℂ
      {P | ∃ a b : Bits m, (∀ i j, (a i j ≠ 0 ∨ b i j ≠ 0) → site i j ∈ F) ∧
        P = pauliXZ a b} := by sorry

end BaconOQEC
