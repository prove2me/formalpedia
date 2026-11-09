-- Prove2me | Theorems.Thm_DepthOneQExp_eq_2_45
-- name    : DepthOneQExp.eq_2_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:47.00271+00:00
-- url     : https://prove2.me/theorems/b88e986f-c507-46fc-8e3c-abba7d85eac9
-- title:
--   Eq. (2.45): $\|\Pi (X_1\otimes X_1 + Z_1\otimes Z_1)\Pi\| = \frac{N-2}{N-1}$ for $n\ge2$
-- statement:
--   Let $n\ge2$ and $N=2^n$, and let
--   $$
--   \Pi=\mathbb E_{P\sim\mu(G_n)}P\otimes P-\mathbb E_{U\sim\mu(U(2^n))}U\otimes\overline U
--   $$
--   (Eq. (2.44)). Then
--   $$
--   \big\|\Pi\,(X_1\otimes X_1+Z_1\otimes Z_1)\,\Pi\big\| = \frac{N-2}{N-1}.
--   $$
--
--   This is the gap of the added Pauli gates on the range of $\Pi$ (the parameter $\varepsilon_B=1-\frac12\cdot\frac{N-2}{N-1}\ge\frac12$ in Lemma 2.16), and the only place where $n\ge2$ is used.
--
--   **Formalization Note** The Haar term is written as $|a_1\rangle\langle a_1|/2^n$ (Eq. (2.41)); the norm is the $L^2$ operator norm.
--
--   Differences from the source:
--   - encoding: E_{U∼µ(U(2ⁿ))} U ⊗ Ū in Π → |a_1⟩⟨a_1|/2ⁿ; reason: the value given by Eq. (2.41)
--   - encoding: E_{P∼µ(G_n)} P ⊗ P → (1/|G_n|) Σ_{P∈G_n} P ⊗ P; reason: µ is the uniform distribution on the finite group
--   - encoding: qubits labelled 1, …, n → qubits labelled 0, …, n − 1 (paper qubit p is index (p − 1) mod n); reason: Lean indexing convention; same gates
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), proof of Theorem 2.13, Eqs. (2.44)–(2.45), p.13

import Mathlib
import Definitions.Def_DepthOneQExp_piProj
import Definitions.Def_DepthOneQExp_hOp

namespace DepthOneQExp

open scoped Matrix.Norms.L2Operator

/-- Eq. (2.45) (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, proof of Theorem 2.13,
Eq. (2.45), p.13): for `n ≥ 2` and `N = 2ⁿ`, `‖Π·(X_1 ⊗ X_1 + Z_1 ⊗ Z_1)·Π‖ = (N − 2)/(N − 1)`, where
`Π = E_{P∼µ(G_n)} P ⊗ P − E_{U∼µ(U(2ⁿ))} U ⊗ Ū` (Eq. (2.44)).

**Formalization Note** `Π` is `piProj n` (the Haar term written as `|a_1⟩⟨a_1|/2ⁿ`, Eq. (2.41)); the
norm is the `L²` operator norm. -/
theorem eq_2_45 (n : ℕ) (hn : 2 ≤ n) :
    ‖piProj n * hOp n * piProj n‖ = ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) := by sorry

end DepthOneQExp
