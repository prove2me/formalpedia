-- Prove2me | Theorems.Thm_BosonicLearn_passive_gaussian_fugacity
-- name    : BosonicLearn.passive_gaussian_fugacity
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-13T20:14:19.055195+00:00
-- url     : https://prove2.me/theorems/49919406-f920-41d5-9bda-90de19224d9b
-- title:
--   Every passive Gaussian state is $\det(I-R)\Gamma(R)$ for a Hermitian $0\preceq R\prec I$
-- statement:
--   The surjectivity half of the bijection of Lemma 2 of the paper.
--
--   Let $\rho$ be a passive Gaussian state on $n$ modes: a Gaussian state whose density operator is block diagonal in the total photon number sectors. Then there is a positive semidefinite $n\times n$ matrix $R$ with $1-R$ positive definite such that
--
--   $$
--   \rho=\det(1-R)\,\Gamma(R).
--   $$
--
--   Status of the other clauses of Lemma 2. That $\det(1-R)\Gamma(R)$ is a passive Gaussian state (with covariance $\tfrac12(1+R)(1-R)^{-1}$ in real form) is `BosonicLearn.fugacity_isGaussianState`; the formula $R=P_1\rho P_1/\operatorname{Tr}(P_0\rho)$, hence uniqueness of $R$, is `BosonicLearn.gammaFock_one_photon`; the mean photon number is `BosonicLearn.fugacity_photon_number`. This statement is the only part of `BosonicLearn.lemma_2` that is not yet proved.
--
--   Possible route. Block diagonality makes the characteristic function invariant under $\zeta\mapsto e^{i\theta}\zeta$, which forces mean $0$ and a covariance $\tfrac12\big(\begin{smallmatrix}\operatorname{Re}C&-\operatorname{Im}C\\ \operatorname{Im}C&\operatorname{Re}C\end{smallmatrix}\big)$ with $C$ Hermitian; put $R=(C-1)(C+1)^{-1}$; positivity and normalization of $\rho$ give $0\preceq R\prec1$; conclude with the fact that a state is determined by its characteristic function (or by its Husimi function, `BosonicLearn.husimi_fourier`).
--
--   **Formalization Note** `IsPassive ρ` is the mission predicate (Gaussian for some mean and covariance, and vanishing Fock matrix elements between different total photon numbers); the conclusion is equality of coefficient arrays with `fugacityCoeff R`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, Eqs. (21)–(22), p. 20

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsPassive

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **Every passive Gaussian state has a fugacity matrix.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "There is a bijection between n-mode passive Gaussian states ρ and n-by-n Hermitian matrices 0 ≤ R < I.
Given R, which we call the fugacity matrix, the corresponding passive Gaussian state is ρ = det(I − R)Γ(R)."

If `ρ` is a passive Gaussian state (Gaussian, and block diagonal in the total photon number), then there is a
positive semidefinite `R` with `1 − R` positive definite such that `ρ = det(1 − R)Γ(R)`.

**Formalization Note.** This is the surjectivity half of the bijection of `lemma_2`; the other clauses of Lemma 2
(`det(1 − R)Γ(R)` is a passive Gaussian state, the formula `R = P_1ρP_1/Tr(P_0ρ)` and hence uniqueness of `R`, and
the mean photon number) are proved in `fugacity_isGaussianState`, `gammaFock_one_photon` and
`fugacity_photon_number`. -/
theorem passive_gaussian_fugacity {n : ℕ} (ρ : State (Occupation (Fin n))) (hρ : IsPassive ρ) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ (1 - R).PosDef ∧
      ρ.coefficients = fugacityCoeff R := by sorry

end BosonicLearn
