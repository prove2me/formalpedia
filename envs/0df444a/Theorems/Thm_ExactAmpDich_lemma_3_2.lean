-- Prove2me | Theorems.Thm_ExactAmpDich_lemma_3_2
-- name    : ExactAmpDich.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:46.49862+00:00
-- url     : https://prove2.me/theorems/ccfc467f-9e51-4355-a158-f0d36cd02c98
-- title:
--   Lemma 3.2 — Clifford rigidity for a product metric
-- statement:
--   Let $G$ be a positive definite $2\times2$ matrix, $G=aI+g_xX+g_yY+g_zZ$, with at least two of the Bloch components $g_r=\mathrm{tr}(G\sigma_r)/2$ nonzero, and let $k\ge1$. Every Clifford unitary $C$ on $k$ qubits with
--
--   $$C\,G^{\otimes k}=G^{\otimes k}\,C$$
--
--   is $C=(V_1\otimes\cdots\otimes V_k)P_\sigma$ for one-qubit Clifford unitaries $V_i$ and a wire permutation $P_\sigma$.
--
--   This rigidity forces the common Holant basis of a nonmonomial entangling library to be diagonal up to a Clifford, which yields the common diagonal Clifford frame.
--
--   Differences from the source:
--   - reading: Clifford unitaries on k qubits → 1 ≤ k; reason: at k = 0 a global phase is Clifford but not an empty product of one-qubit Cliffords
--   - encoding: "whose Bloch vector has at least two nonzero Pauli components" → at least two of tr(GX), tr(GY), tr(GZ) are nonzero; reason: g_r = tr(Gσ_r)/2
--   - encoding: one-qubit Cliffords, Clifford with arbitrary phases → members of QAlgorithms.Clifford.normalizer 1 (matrices on Qubits 1, read on Bool via fun _ => b); reason: same objects
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Lemma 3.2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_ExactAmpDich_QTract

set_option autoImplicit false

namespace ExactAmpDich

open QAlgorithms
open scoped ComplexOrder

/-- **Lemma 3.2 (Clifford rigidity for a product metric).** Liu–Meng, *A Dichotomy for Exact Quantum Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Lemma 3.2, p.10 (PDF p.11): "Let G
be a positive definite 2 × 2 matrix whose Bloch vector has at least two nonzero Pauli components.
Every Clifford unitary commuting with G⊗k is a product of one-qubit Cliffords and a wire
permutation."

The Bloch components of `G = aI + g_x X + g_y Y + g_z Z` are `g_r = tr(G σ_r)/2`; "at least two
nonzero" is: at least two of `tr(GX)`, `tr(GY)`, `tr(GZ)` are nonzero.

**Formalization Note.** `k ≥ 1` (at `k = 0` a global phase is not an empty product). Clifford is
membership in `QAlgorithms.Clifford.normalizer`, phases included; a one-qubit Clifford `V i` is a
matrix on `Qubits 1`, read on `Bool` through `fun _ => b`. -/
theorem lemma_3_2 (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (hBloch : 2 ≤ (Finset.univ.filter fun P : Fin 3 =>
      (G * ![Stabilizer.Pauli.X.mat, Stabilizer.Pauli.Y.mat, Stabilizer.Pauli.Z.mat] P).trace ≠ 0).card)
    {k : ℕ} (hk : 1 ≤ k) (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : (C : Matrix (Qubits k) (Qubits k) ℂ) * tensorPow G k =
      tensorPow G k * (C : Matrix (Qubits k) (Qubits k) ℂ)) :
    ∃ (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ) (σ : Equiv.Perm (Fin k)),
      (∀ i, V i ∈ Clifford.normalizer 1) ∧
      (C : Matrix (Qubits k) (Qubits k) ℂ) =
        tensorProd (fun i y x => (V i : Matrix (Qubits 1) (Qubits 1) ℂ) (fun _ => y) (fun _ => x)) *
          factorPerm σ := by sorry

end ExactAmpDich
