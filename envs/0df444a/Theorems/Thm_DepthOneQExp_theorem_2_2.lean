-- Prove2me | Theorems.Thm_DepthOneQExp_theorem_2_2
-- name    : DepthOneQExp.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:51:25.382512+00:00
-- url     : https://prove2.me/theorems/62959680-b3a1-4946-9d18-a24ad8b10da5
-- title:
--   Theorem 2.2: sixteen depth-1 $X$/$Z$/CNOT circuits on $3s$ qubits form a quantum expander with spectral gap at least $1/(2\cdot10^8)$
-- statement:
--   For every integer $s\ge1$, the sixteen $3s$-qubit matrices $U_1,\dots,U_{16}$ of Eqs. (2.1)–(2.6) —
--   $$
--   U_1=X\otimes I,\ U_2=Z\otimes I,\ U_3=\mathrm{CNOT}_{1,2},\ U_4=\mathrm{CNOT}_{2,1},\ U_5=\mathrm{CNOT}_{2,3},\ U_6=\mathrm{CNOT}_{3,2},
--   $$
--   $U_7,\dots,U_{12}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+a,3i+b}$ ($1\le a\ne b\le3$), and $U_{13},\dots,U_{16}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+4,3i+2},\ \mathrm{CNOT}_{3i+5,3i+1},\ \mathrm{CNOT}_{3i+5,3i+3},\ \mathrm{CNOT}_{3i+6,3i+2}$ with indices mod $3s$ — satisfy:
--
--   1. every $U_i$ is unitary;
--   2. $\{U_1,\dots,U_{16}\}$ forms a quantum expander on $3s$ qubits with spectral gap at least $1/(2\cdot10^8)$, i.e.
--   $$
--   \sigma_2\Big(\frac1{16}\sum_{i=1}^{16}U_i\otimes\overline{U_i}\Big)\le 1-\frac1{2\cdot10^8};
--   $$
--   3. every $U_i$ can be written as a depth-1 circuit of $X$, $Z$ and CNOT gates.
--
--   The number of gates per layer, the depth and the gap are all independent of the number of qubits $3s$.
--
--   **Formalization Note** The existential "there exists a set of 16 unitaries" is witnessed by the paper's explicit formulas, which are the definition `U s`. A depth-1 circuit is a non-empty layer of gates from $\{X,Z,\mathrm{CNOT}\}$ on pairwise disjoint qubits (the published `MITMSynthesis.depthOneSet`).
--
--   Differences from the source:
--   - encoding: "there exists a set of 16 unitary matrices … Moreover specifically U_1 = …, U_16 = …" → the explicit family U s : Fin 16 → matrices of (2.1)–(2.6); reason: the paper names the witness; the existential is a consequence
--   - encoding: "spectral gap of at least 1/(2·10⁸)" via Definition 2.1 (second singular value) → IsQuantumExpanderGap (U s) (1/(2·10⁸)): ‖(1/16) Σ U_i ⊗ Ū_i − |a_1⟩⟨a_1|/2^{3s}‖ ≤ 1 − 1/(2·10⁸); reason: for unitary families this norm is the second singular value (sanity check: (U ⊗ Ū)a_1 = a_1)
--   - encoding: a set {U_1, …, U_16} → an indexed family of 16 (repetitions count; for s = 1 some U_i coincide); reason: the paper averages over 16 terms
--   - encoding: U_7, …, U_12 for 1 ≤ a ≠ b ≤ 3 in unspecified order → lexicographic order of (a, b); reason: the expander property and depth do not depend on the order
--   - encoding: "can be written as a depth-1 circuit" (gates Pauli or CNOT, Theorem 1.2) → ∈ depthOneSet (3s) {X, Z, CNOT}: a non-empty layer of gates from {X, Z, CNOT} on disjoint qubits; reason: the published depth-one model; every U_i has at least one gate
--   - encoding: qubits labelled 1, …, n → qubits labelled 0, …, n − 1 (paper qubit p is index (p − 1) mod n); reason: Lean indexing convention; same gates
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.2, Eqs. (2.1)–(2.6), pp.6–7

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_DepthOneQExp_xGate
import Definitions.Def_DepthOneQExp_zGate
import Definitions.Def_DepthOneQExp_cnotGate
import Definitions.Def_DepthOneQExp_U
import Definitions.Def_DepthOneQExp_IsQuantumExpanderGap

namespace DepthOneQExp

/-- **Theorem 2.2** (Depth-1 constant-sized quantum expanders with constant spectral gaps)
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.2,
Eqs. (2.1)–(2.6), pp.6–7): for every integer `s ≥ 1`, the sixteen `3s`-qubit matrices
`U_1, …, U_16` of (2.1)–(2.6) are unitary, form a quantum expander on `3s` qubits with a spectral
gap of at least `1/(2·10⁸)`, and each `U_i` can be written as a depth-1 circuit of `X`, `Z` and
`CNOT` gates.

**Formalization Note** The paper's "there exists a set of 16 unitaries … Moreover specifically
`U_1 = …`" is stated for the explicit family `U s` of (2.1)–(2.6) (0-based periodic qubit indices).
The expander property is `IsQuantumExpanderGap` (Definition 2.1 with the second singular value
`≤ 1 − Δ`). A depth-1 circuit is a non-empty layer of gates from `{X, Z, CNOT}` on pairwise disjoint
qubits (`MITMSynthesis.depthOneSet`). -/
theorem theorem_2_2 (s : ℕ) (hs : 1 ≤ s) :
    (∀ i, U s i ∈ Matrix.unitaryGroup (MITMSynthesis.Q (3 * s)) ℂ) ∧
    IsQuantumExpanderGap (U s) (1 / (2 * 10 ^ 8)) ∧
    (∀ i, U s i ∈ MITMSynthesis.depthOneSet (3 * s) {xGate, zGate, cnotGate}) := by sorry

end DepthOneQExp
