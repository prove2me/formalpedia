-- Prove2me | Theorems.Thm_DepthOneQExp_eq_2_51_2_52
-- name    : DepthOneQExp.eq_2_51_2_52
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:52.76762+00:00
-- url     : https://prove2.me/theorems/a254f3aa-951a-4113-a9f1-0ec9e2316eea
-- title:
--   Eqs. (2.51)–(2.52): the Gram matrices $M^\dagger M$, $M^\dagger H M$ and $\det(M^\dagger HM - \lambda M^\dagger M)$
-- statement:
--   Let $n\ge2$, $N=2^n$, $r=1/\sqrt N$, $H=X_1\otimes X_1+Z_1\otimes Z_1$, and let $M=\sum_{i=1}^5|a_i\rangle\langle i|$ be the matrix with columns $|a_1\rangle,\dots,|a_5\rangle$. Then
--
--   1. $$M^\dagger M=\begin{pmatrix}N&1&1&r&r\\1&1&r^2&r&r\\1&r^2&1&r&r\\r&r&r&1&r^2\\r&r&r&r^2&1\end{pmatrix},\qquad M^\dagger HM=\begin{pmatrix}2N&2&2&2r&2r\\2&1&2r^2&r&r\\2&2r^2&1&r&r\\2r&r&r&0&2r^2\\2r&r&r&2r^2&0\end{pmatrix};$$
--   2. for every scalar $\lambda$,
--   $$
--   \det\big(M^\dagger HM-\lambda M^\dagger M\big) = -\frac{N-2}{N^4}\,(\lambda-2)\,\big(\lambda(N-1)+2\big)^2\,\big(\lambda(N-1)-N+2\big)^2 .
--   $$
--
--   These give the eigenvalues of the compression of $H$ to $\mathrm{span}\{|a_i\rangle\}$: one eigenvalue $2$, two eigenvalues $-2/(N-1)$ and two eigenvalues $(N-2)/(N-1)$.
--
--   **Formalization Note** The scalar $\lambda$ is named $t$ and ranges over $\mathbb C$.
--
--   Differences from the source:
--   - encoding: scalar λ → t : ℂ; reason: λ is a Lean keyword; complex scalars include the real ones of the paper
--   - encoding: qubits labelled 1, …, n → qubits labelled 0, …, n − 1 (paper qubit p is index (p − 1) mod n); reason: Lean indexing convention; same gates
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), proof of Theorem 2.13, Eqs. (2.51)–(2.52), p.14

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_aVec
import Definitions.Def_DepthOneQExp_hOp

namespace DepthOneQExp

open Matrix

/-- Eqs. (2.51)–(2.52) (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary
group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, proof of
Theorem 2.13, p.14): for `n ≥ 2`, `N = 2ⁿ`, `r = 1/√N`, `H = X_1 ⊗ X_1 + Z_1 ⊗ Z_1` and
`M = Σ_{i=1}^5 |a_i⟩⟨i|` (the matrix with columns `|a_1⟩, …, |a_5⟩`),
(a) `M†M` and `M†HM` are the two displayed `5 × 5` matrices of (2.51), and
(b) for every scalar `λ`,
`det(M†HM − λM†M) = −((N − 2)/N⁴)·(λ − 2)·(λ(N − 1) + 2)²·(λ(N − 1) − N + 2)²`.

**Formalization Note** `λ` is named `t` (`λ` is a Lean keyword); scalars are complex. -/
theorem eq_2_51_2_52 (n : ℕ) (hn : 2 ≤ n) :
    let N : ℂ := 2 ^ n
    let r : ℂ := ((Real.sqrt (2 ^ n))⁻¹ : ℝ)
    let M : Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (Fin 5) ℂ :=
      Matrix.of fun p i => aVec n i p
    Mᴴ * M = !![N, 1, 1, r, r; 1, 1, r ^ 2, r, r; 1, r ^ 2, 1, r, r; r, r, r, 1, r ^ 2;
      r, r, r, r ^ 2, 1] ∧
    Mᴴ * hOp n * M = !![2 * N, 2, 2, 2 * r, 2 * r; 2, 1, 2 * r ^ 2, r, r; 2, 2 * r ^ 2, 1, r, r;
      2 * r, r, r, 0, 2 * r ^ 2; 2 * r, r, r, 2 * r ^ 2, 0] ∧
    ∀ t : ℂ, (Mᴴ * hOp n * M - t • (Mᴴ * M)).det =
      -((N - 2) / N ^ 4) * (t - 2) * (t * (N - 1) + 2) ^ 2 * (t * (N - 1) - N + 2) ^ 2 := by sorry

end DepthOneQExp
