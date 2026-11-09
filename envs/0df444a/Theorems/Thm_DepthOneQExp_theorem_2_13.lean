-- Prove2me | Theorems.Thm_DepthOneQExp_theorem_2_13
-- name    : DepthOneQExp.theorem_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:14.444208+00:00
-- url     : https://prove2.me/theorems/000d5aa0-349c-4e42-814a-47f2748ff482
-- title:
--   Theorem 2.13: adding $X\otimes I$ and $Z\otimes I$ to a CNOT-group 2-design gives a quantum expander with gap $\ge \frac{\min(m\varepsilon,2)}{24(m+2)}$
-- statement:
--   Let $n\ge2$ and suppose $P_1,\dots,P_m\in G_n$ satisfy
--   $$
--   \Big\|\frac1m\sum_{i=1}^m P_i\otimes P_i-\mathbb E_{P\sim\mu(G_n)}P\otimes P\Big\|\le 1-\varepsilon .
--   $$
--   Let $P_{m+1}=X\otimes I_{2^{n-1}}$ and $P_{m+2}=Z\otimes I_{2^{n-1}}$. Then $\{P_1,\dots,P_{m+2}\}$ forms a quantum expander on $n$ qubits with a spectral gap of at least
--   $$
--   \frac{\min(m\varepsilon,\,2)}{24(m+2)} .
--   $$
--
--   This is the augmentation step: a constant-size, constant-gap "2-design" on the CNOT group becomes a quantum expander on the full unitary group after adding two single-qubit Pauli gates.
--
--   **Formalization Note** The family of $m+2$ matrices is indexed (the $m$ permutation matrices followed by $X_1$, $Z_1$); $X$ and $Z$ act on qubit 1. "Spectral gap at least $\Delta$" is the predicate `IsQuantumExpanderGap`. No inverse-closure of the $P_i$ is assumed, as in the paper.
--
--   Differences from the source:
--   - encoding: the set {P_1, …, P_{m+2}} → the indexed family Fin.append (P_i) [X_1, Z_1] of m + 2 matrices; reason: the paper averages over m + 2 terms with multiplicity (Eq. (2.46))
--   - encoding: "forms a quantum expander with a spectral gap of at least Δ" (Definition 2.1, Δ > 0) → IsQuantumExpanderGap: ‖(1/(m+2)) Σ P_i ⊗ P̄_i − |a_1⟩⟨a_1|/2ⁿ‖ ≤ 1 − Δ, ε any real; reason: for unitaries this is σ₂ ≤ 1 − Δ (see the definition); for ε ≤ 0 the claimed gap is ≤ 0 and the inequality is the trivial σ₂ ≤ 1
--   - encoding: E_{P∼µ(G_n)} P ⊗ P → (1/|G_n|) Σ_{P∈G_n} P ⊗ P; reason: µ is the uniform distribution on the finite group
--   - encoding: qubits labelled 1, …, n → qubits labelled 0, …, n − 1 (paper qubit p is index (p − 1) mod n); reason: Lean indexing convention; same gates
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.13, Eq. (2.28), p.11

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_xPerm
import Definitions.Def_DepthOneQExp_zMat
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotAvg
import Definitions.Def_DepthOneQExp_IsQuantumExpanderGap

namespace DepthOneQExp

open scoped Matrix.Norms.L2Operator Kronecker

/-- Theorem 2.13 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.13, Eq. (2.28),
p.11): let `n ≥ 2` and suppose `P_1, …, P_m ∈ G_n` satisfy
`‖(1/m) Σ_{i=1}^m P_i ⊗ P_i − E_{P∼µ(G_n)} P ⊗ P‖ ≤ 1 − ε`. Let `P_{m+1} = X ⊗ I_{2^{n−1}}` and
`P_{m+2} = Z ⊗ I_{2^{n−1}}`. Then `{P_1, …, P_{m+2}}` forms a quantum expander on `n` qubits with a
spectral gap of at least `min(mε, 2) / (24(m + 2))`.

**Formalization Note** The family is indexed (`Fin.append` of the `m` permutation matrices and
`[X_1, Z_1]`); `X`, `Z` act on qubit 1 (0-based index `0`). "Spectral gap at least `Δ`" is
`IsQuantumExpanderGap` (second singular value `≤ 1 − Δ`). `ε` is any real number; no inverse
closure of the `P_i` is assumed (none is printed). -/
theorem theorem_2_13 (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (P : Fin m → cnotGroup n) (ε : ℝ)
    (hP : ‖(1 / (m : ℂ)) • ∑ i, (permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ
        permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n))) - cnotAvg n‖ ≤ 1 - ε) :
    IsQuantumExpanderGap
      (Fin.append (fun i => permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n)))
        ![permToMatrix (xPerm n 0), zMat n 0])
      (min (m * ε) 2 / (24 * (m + 2))) := by sorry

end DepthOneQExp
