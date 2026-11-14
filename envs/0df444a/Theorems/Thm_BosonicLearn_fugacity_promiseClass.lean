-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_promiseClass
-- name    : BosonicLearn.fugacity_promiseClass
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:38:31.223486+00:00
-- url     : https://prove2.me/theorems/cf006675-56d9-44c4-898b-de016a6e1515
-- title:
--   $R\succeq\frac{\nu}{1+\nu}I$ implies $\Sigma\succeq(\tfrac12+\nu)I$ for the passive Gaussian state $\rho_R=\det(I-R)\Gamma(R)$
-- statement:
--   The covariance of a passive Gaussian state is bounded below through its fugacity matrix.
--
--   Let $R$ be a Hermitian $n\times n$ matrix with $0\preceq R\prec\mathbf 1$ and let $\nu>0$ be such that
--
--   $$
--   R\succeq\frac{\nu}{1+\nu}\,\mathbf 1 .
--   $$
--
--   Then the passive Gaussian state $\rho_R=\det(\mathbf 1-R)\,\Gamma(R)$ has covariance matrix $\Sigma\succeq(\tfrac12+\nu)\mathbf 1$; that is, $\rho_R$ belongs to the promise class $K(n,\nu)$.
--
--   Why it holds. $\rho_R$ is the gauge-invariant Gaussian state with $\langle a_i^\dagger a_j\rangle$ given by the entries of $\bar N=R(\mathbf 1-R)^{-1}$ (up to transposition), so the eigenvalues of $\Sigma$ are $\tfrac12+\lambda/(1-\lambda)$, each twice, for $\lambda$ in the spectrum of $R$. The function $\lambda\mapsto\lambda/(1-\lambda)$ is increasing on $[0,1)$ and equals $\nu$ at $\lambda=\nu/(1+\nu)$.
--
--   Role. Together with Lemma 2 this shows that the hard family $R_X=r(\mathbf 1+\xi X)$, $r=\nu/((1-4\xi)(1+\nu))$, $\|X\|_{\mathrm{op}}\le4$, lies in the promise class (`BosonicLearn.fugacityFamily_promiseClass`), since $R_X\succeq r(1-4\xi)\mathbf 1=\frac{\nu}{1+\nu}\mathbf 1$.
--
--   **Formalization Note** $\rho$ is any `State` whose coefficient array is `fugacityCoeff R`; its existence and passivity are Lemma 2 (`BosonicLearn.lemma_2`) and are not asserted here. The hypotheses are `R.PosSemidef`, `(1 − R).PosDef` and `(R − (ν/(1+ν)) • 1).PosSemidef` over $\mathbb C$ (`ComplexOrder`); the conclusion is `ρ ∈ promiseClass n ν`, i.e. `IsGaussianState ρ μ S` for some `μ, S` with `S − (1/2 + ν) • 1` positive semidefinite.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, p. 20 (fugacity matrix, mean photon number Tr[R(I − R)^{−1}]); §5.1, p. 30 (choice of r); proof of Theorem 5, p. 40

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix
open scoped ComplexOrder

namespace BosonicLearn

/-- **Covariance of a passive Gaussian state from its fugacity matrix.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20 ("the mean total photon number of ρ is Tr(ρ n̂) = Tr[R(I − R)^{−1}]"), and §5.1, p. 30: the
family `R_X = r(I + ξX)` with `r = ν/((1 − 4ξ)(1 + ν))` has covariance `Σ ⪰ (1/2 + ν)I`.

Let `R` be a Hermitian `n × n` matrix with `0 ⪯ R ≺ I` and `R ⪰ (ν/(1 + ν)) I`, `ν > 0`. Then the passive Gaussian
state `ρ_R = det(I − R)Γ(R)` has covariance matrix `Σ ⪰ (1/2 + ν) I`: it belongs to the promise class `K(n, ν)`.

**Formalization Note.** `ρ` is any `State` with coefficient array `fugacityCoeff R` (it exists by `lemma_2`).
The matrix of second moments `⟨a_i† a_j⟩` of `ρ_R` is `R(I − R)^{−1}` up to transposition, the covariance matrix has
eigenvalues `1/2 + λ/(1 − λ)` (each twice) for `λ` in the spectrum of `R`, and `λ ≥ ν/(1 + ν)` gives
`λ/(1 − λ) ≥ ν`. -/
theorem fugacity_promiseClass {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (ν : ℝ) (hν : 0 < ν)
    (hRν : (R - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (ρ : State (Occupation (Fin n))) (hρ : ρ.coefficients = fugacityCoeff R) :
    ρ ∈ promiseClass n ν := by sorry

end BosonicLearn
