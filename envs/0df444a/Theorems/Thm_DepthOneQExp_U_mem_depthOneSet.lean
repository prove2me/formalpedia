-- Prove2me | Theorems.Thm_DepthOneQExp_U_mem_depthOneSet
-- name    : DepthOneQExp.U_mem_depthOneSet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T05:17:23.926698+00:00
-- url     : https://prove2.me/theorems/8699483a-d07d-4973-a3e3-b66e9e84ff32
-- title:
--   Each $U_i$ of Theorem 2.2 is a depth-1 circuit of $X$, $Z$, CNOT gates
-- statement:
--   Let $s\ge 1$ and $n=3s$, and let $U_1,\dots,U_{16}$ be the $n$-qubit unitaries of Theorem 2.2 (Eqs. (2.1)–(2.6)), with qubit indices taken periodically modulo $3s$:
--
--   1. $U_1=X\otimes I$ and $U_2=Z\otimes I$, the Pauli $X$ and $Z$ gates on qubit $1$;
--   2. $U_3,\dots,U_6=\mathrm{CNOT}_{1,2},\mathrm{CNOT}_{2,1},\mathrm{CNOT}_{2,3},\mathrm{CNOT}_{3,2}$;
--   3. $U_7,\dots,U_{12}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+a,3i+b}$ for $1\le a\ne b\le 3$;
--   4. $U_{13},\dots,U_{16}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+4,3i+2},\ \prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+5,3i+1},\ \prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+5,3i+3},\ \prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+6,3i+2}$.
--
--   Then every $U_i$ is a **depth-1 circuit** over the gate set $\{X, Z, \mathrm{CNOT}\}$: it is the product of a non-empty list of gates from this set placed on pairwise disjoint sets of qubits,
--
--   $$
--   U_i\in V_{3s,\{X,Z,\mathrm{CNOT}\}}\qquad (1\le i\le 16).
--   $$
--
--   This is the depth clause of Theorem 2.2; the remaining clauses (unitarity and the spectral gap $1/(2\cdot 10^8)$) are proved separately.
--
--   **Formalization Note** The $U_i$ are defined (`DepthOneQExp.U`) as products of register-level permutation and diagonal matrices, not as circuits, so the statement is not true by definition. $V_{n,G}$ is `MITMSynthesis.depthOneSet n G`: a non-empty list of placed gates from $G$ with pairwise disjoint qubit ranges, whose unitary is the product of the placed gates. Qubits are 0-based, the paper's qubit $p$ being index $(p-1) \bmod 3s$; `U s k` is the paper's $U_{k+1}$.
-- source:
--   Anshu, Balasubramanian, Haferkamp, Harrow, Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605, Theorem 2.2 and Eqs. (2.1)-(2.6), pp. 6-7 ('each U_i can be written as a depth-1 circuit')

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_DepthOneQExp_xGate
import Definitions.Def_DepthOneQExp_zGate
import Definitions.Def_DepthOneQExp_cnotGate
import Definitions.Def_DepthOneQExp_U

namespace DepthOneQExp

/-- Depth-one clause of Theorem 2.2 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, arXiv:2609.01605,
Theorem 2.2, Eqs. (2.1)–(2.6), pp.6–7): for `s ≥ 1`, each of the sixteen `3s`-qubit unitaries
`U_1, …, U_16` is the unitary of a depth-one circuit over `{X, Z, CNOT}`. -/
theorem U_mem_depthOneSet (s : ℕ) (hs : 1 ≤ s) (i : Fin 16) :
    U s i ∈ MITMSynthesis.depthOneSet (3 * s) {xGate, zGate, cnotGate} := by sorry

end DepthOneQExp
