-- Prove2me | Theorems.Thm_CompNonlocal_lemma_1_rank_one_effects
-- name    : CompNonlocal.lemma_1_rank_one_effects
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:25.734486+00:00
-- url     : https://prove2.me/theorems/5f59bc60-2754-4475-a963-a8f49c61c427
-- title:
--   Lemma 1, p.26 — measuring all output qubits gives rank-one effects
-- statement:
--   Let $U$ be a unitary on an input register $A$ and auxiliary qubits $W$ initialized to $|0\rangle_W$. If every output qubit is measured in the computational basis, the effect on $A$ of the full record $a$ is
--   $$E_a=(I_A\otimes\langle0|_W)\,U^\dagger|a\rangle\langle a|U\,(I_A\otimes|0\rangle_W).$$
--   Then $\sum_aE_a=I_A$, and every nonzero $E_a$ has rank one and equals $\eta_aP_a$ with $\eta_a=\operatorname{Tr}E_a$ and $P_a$ a rank-one orthogonal projector.
--
--   This is why the §8.1 receiver, which measures everything except $Q$, leaves $Q$ in a pure state.
--
--   Differences from the source:
--   - generalization: U a unitary circuit; A a register of qubits → U any unitary matrix on ι × {0,1}^{n_W}; A any finite-dimensional register with basis ι; reason: the proof uses only unitarity; circuits on qubits are the instance ι = {0,1}^{n_A}
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 1, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

open scoped Matrix

namespace CompNonlocal

open QAlgorithms.Complexity

/-- **Lemma 1 (Measuring all output qubits gives rank-one effects).** Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), p.26: "Let U be a unitary circuit acting on an arbitrary input
register A and auxiliary registers W initialized to |0⟩_W. If every output qubit is measured in the
computational basis, the effect on A corresponding to the full record a is
E_a = (I_A ⊗ ⟨0|_W)U† |a⟩⟨a| U(I_A ⊗ |0⟩_W). These effects satisfy Σ_a E_a = I_A. Every nonzero
effect has rank one and can be written E_a = η_a P_a, where η_a = Tr(E_a) and P_a is a rank-one
projector."

**Formalization Note** The input register `A` has an arbitrary finite basis `ι`, the auxiliary
register is `nW` qubits (`|0⟩_W` = all `false`), and `U` is any unitary on `ι × Bits nW` (a circuit
is a special case). The record `a` ranges over the computational basis of all output qubits; entry
`(i, j)` of `E_a` is `conj(U_{a,(i,0)}) · U_{a,(j,0)}`. -/
theorem lemma_1_rank_one_effects {ι : Type} [Fintype ι] [DecidableEq ι] (nW : ℕ)
    (U : Matrix (ι × Bits nW) (ι × Bits nW) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (ι × Bits nW) ℂ) :
    let E : ι × Bits nW → Matrix ι ι ℂ := fun a =>
      Matrix.of fun i j => star (U a (i, fun _ => false)) * U a (j, fun _ => false)
    (∑ a, E a = 1) ∧
      ∀ a, E a ≠ 0 →
        (E a).rank = 1 ∧
          ∃ P : Matrix ι ι ℂ, P * P = P ∧ Pᴴ = P ∧ P.rank = 1 ∧ E a = (E a).trace • P := by sorry

end CompNonlocal
