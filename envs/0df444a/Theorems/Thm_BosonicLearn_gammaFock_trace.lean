-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_trace
-- name    : BosonicLearn.gammaFock_trace
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:14:53.59939+00:00
-- url     : https://prove2.me/theorems/665c438e-4ded-42b5-820c-9d7b9cc14670
-- title:
--   Trace of $\Gamma$ of a diagonal contraction: $\sum_u\langle u|\Gamma(\mathrm{diag}\,d)|u\rangle=\prod_i(1-d_i)^{-1}$
-- statement:
--   The normalization of the fugacity form of a passive Gaussian state, in the diagonal case.
--
--   For $d_1,\dots,d_n\in[0,1)$,
--
--   $$
--   \sum_{u\in\mathbb N^n}\langle u|\Gamma(\mathrm{diag}(d_1,\dots,d_n))|u\rangle=\prod_{i=1}^n\frac1{1-d_i}=\frac1{\det(I-\mathrm{diag}\,d)} .
--   $$
--
--   Role. In Lemma 2 of the paper the state is $\det(I-R)\Gamma(R)$; the factor $\det(I-R)$ is $1/\operatorname{Tr}\Gamma(R)$. This is the diagonal case; the Hermitian case follows by unitary diagonalization with `BosonicLearn.gammaFock_mul`.
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock`; the statement is a `HasSum` over all occupation vectors with value the complex cast of the real product $\prod_i(1-d_i)^{-1}$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Trace of `Γ` of a diagonal contraction: `Tr Γ(diag d) = ∏ᵢ (1 − dᵢ)⁻¹`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "the corresponding passive Gaussian state is ρ = det(I − R)Γ(R)"; the factor
`det(I − R)` is the normalization `1/Tr Γ(R)`.

For `d₁, …, dₙ ∈ [0, 1)`, the diagonal Fock entries of `Γ(diag d)` are `∏ᵢ dᵢ^{uᵢ}` and they sum, over all occupation
vectors `u ∈ ℕⁿ`, to `∏ᵢ (1 − dᵢ)⁻¹ = 1/det(1 − diag d)`.

**Formalization Note.** Diagonal case of `Tr Γ(R) = 1/det(1 − R)`; the general Hermitian case follows by
unitary diagonalization and `gammaFock_mul`. The value is the complex cast of the real product. -/
theorem gammaFock_trace {n : ℕ} (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Occupation (Fin n) => gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u)
      (∏ i, ((1 - d i)⁻¹ : ℝ)) := by sorry

end BosonicLearn
