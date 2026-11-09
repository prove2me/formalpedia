-- Prove2me | Theorems.Thm_DepthOneQExp_eq_2_43
-- name    : DepthOneQExp.eq_2_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:56.869406+00:00
-- url     : https://prove2.me/theorems/54923730-1ff7-4a54-b919-cd2363e3188f
-- title:
--   Eq. (2.43): $\mathbb E_{P\sim\mu(G_n)} P\otimes P = \sum_{i=1}^5 |b_i\rangle\langle b_i|$
-- statement:
--   Let $n\ge2$. Let $|b_1\rangle,\dots,|b_5\rangle$ be the Gram–Schmidt orthonormalization of $|a_1\rangle=\sum_i|i\rangle|i\rangle$, $|a_2\rangle=|+^n\rangle|+^n\rangle$, $|a_3\rangle=|0^n\rangle|0^n\rangle$, $|a_4\rangle=|0^n\rangle|+^n\rangle$, $|a_5\rangle=|+^n\rangle|0^n\rangle$. Then
--   $$
--   \mathbb E_{P\sim\mu(G_n)}P\otimes P = \sum_{i=1}^5|b_i\rangle\langle b_i| ,
--   $$
--   the orthogonal projector onto $\mathrm{span}\{|a_1\rangle,\dots,|a_5\rangle\}$.
--
--   It reduces the second-moment operator of the CNOT group to an explicit rank-5 projector, which is what makes Eq. (2.45) computable.
--
--   **Formalization Note** $\sum_i|b_i\rangle\langle b_i|$ is stated as the orthogonal projector onto the span (equal for every orthonormal basis of the span).
--
--   Differences from the source:
--   - encoding: Σ_{i=1}^5 |b_i⟩⟨b_i| with b_i the Gram–Schmidt vectors → the matrix of the orthogonal projection onto span{a_1, …, a_5}; reason: the two are equal for any orthonormal basis of the span
--   - encoding: E_{P∼µ(G_n)} P ⊗ P → (1/|G_n|) Σ_{P∈G_n} P ⊗ P; reason: µ is the uniform distribution on the finite group
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), proof of Theorem 2.13, Eq. (2.43), p.13

import Mathlib
import Definitions.Def_DepthOneQExp_cnotAvg
import Definitions.Def_DepthOneQExp_spanProj

namespace DepthOneQExp

/-- Eq. (2.43) (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, proof of Theorem 2.13,
Eq. (2.43), p.13): for `n ≥ 2`, `E_{P∼µ(G_n)} P ⊗ P = Σ_{i=1}^5 |b_i⟩⟨b_i|`, the orthogonal projector
onto `span{|a_1⟩, …, |a_5⟩}` (`|b_i⟩` the Gram–Schmidt orthonormalization of the `|a_i⟩`).

**Formalization Note** `Σ_i |b_i⟩⟨b_i|` is `spanProj n`, the matrix of the orthogonal projection onto
the span (equal to `Σ_i |b_i⟩⟨b_i|` for any orthonormal basis of the span). -/
theorem eq_2_43 (n : ℕ) (hn : 2 ≤ n) : cnotAvg n = spanProj n := by sorry

end DepthOneQExp
