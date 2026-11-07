-- Prove2me | Theorems.Thm_ExactAmpDich_lemma_A_1
-- name    : ExactAmpDich.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:21.848915+00:00
-- url     : https://prove2.me/theorems/ef849323-269f-4e59-803f-dbd489ffc09e
-- title:
--   Lemma A.1 — product-preserving unitaries are $(V_1\otimes\cdots\otimes V_k)P$
-- statement:
--   Let $U$ be a unitary on $k\ge1$ qubits. Then $U$ maps every product state to a product state if and only if
--
--   $$U=(V_1\otimes\cdots\otimes V_k)\,P_\sigma$$
--
--   for one-qubit unitaries $V_1,\dots,V_k$ and a permutation matrix $P_\sigma$ of the $k$ tensor factors.
--
--   This turns the product-preserving class $\mathrm{ProdPerm}$ of Theorem 1.1, defined by quantifying over all product inputs, into an explicit normal form.
--
--   Differences from the source:
--   - reading: "A k-qubit unitary" → 1 ≤ k; reason: every gate of a library acts on at least one qubit; at k = 0 a global phase c ≠ 1 preserves product states but is not an empty tensor product times a permutation
--   - encoding: (U₁ ⊗ ⋯ ⊗ U_k)P with P permuting the tensor factors → tensorProd V * factorPerm σ with P_σ|x⟩ = |x ∘ σ⟩ and V i unitary 2 × 2 matrices; reason: every factor permutation is some P_σ; same instances
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Lemma A.1, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ExactAmpDich_QTract

set_option autoImplicit false

namespace ExactAmpDich

open QAlgorithms

/-- **Lemma A.1 (Product-preserving unitaries).** Liu–Meng, *A Dichotomy for Exact Quantum Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Lemma A.1, p.18 (PDF p.19): "A k-qubit
unitary preserves all product states if and only if it has the form (U1 ⊗· · · ⊗Uk)P, where the Uj
are one-qubit unitaries and P permutes the tensor factors."

**Formalization Note.** `k ≥ 1`, as for every gate of a library: at `k = 0` a nontrivial global
phase preserves product states but is not an empty tensor product. The permutation matrix is
`factorPerm σ`, `P_σ |x⟩ = |x ∘ σ⟩`; every permutation of the factors arises for some `σ`. -/
theorem lemma_A_1 {k : ℕ} (hk : 1 ≤ k) (U : Matrix (Qubits k) (Qubits k) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    PreservesProduct U ↔ ∃ (V : Fin k → Matrix Bool Bool ℂ) (σ : Equiv.Perm (Fin k)),
      (∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) ∧ U = tensorProd V * factorPerm σ := by sorry

end ExactAmpDich
