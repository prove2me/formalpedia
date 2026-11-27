-- Prove2me | Theorems.Thm_BosonicResources_pure_iff_det
-- name    : BosonicResources.pure_iff_det
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:46:12.490499+00:00
-- url     : https://prove2.me/theorems/6498b30f-3bf7-574c-bc7b-24be13eb2bec
-- title:
--   A Gaussian state is pure if and only if $\det\Sigma=4^{-n}$
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). A state is *pure* if it is a rank-one projector $\lvert\psi\rangle\langle\psi\rvert$ with $\psi$ a unit vector.
--
--   Let $\rho=\rho(\mu,\Sigma)$ be an $n$-mode Gaussian state. Then
--
--   $$
--   \rho\ \text{is pure}\quad\Longleftrightarrow\quad\det\Sigma=4^{-n}.
--   $$
--
--   The statement connects the operator definition of purity, which is the one used in the hypotheses of Theorem 3, Theorem 5 and Lemma B.3, with the paper's description of pure Gaussian states through their covariance matrices. It is consistent with the convention that the vacuum, a pure state, has covariance $\tfrac12 I$, of determinant $4^{-n}$.
--
--   **Formalization Note** "Valid $\Sigma$" is the hypothesis that $\Sigma$ is the covariance of the Gaussian state $\rho$ (`BosonicLearn.IsGaussianState`). Sec. 2 prints the "if" direction and App. A the equivalence; the equivalence is what is stated. Purity is `IsPure`, the right-hand side is written $(1/4)^{n}$, and no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (covariance matrices of pure Gaussian states); App. A (valid covariance matrices)

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsPure
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **A Gaussian state is pure if and only if `det Σ = 4^{-n}`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "Given a 2n by 2n real positive definite matrix Σ, the necessary and sufficient conditions for it to be a
covariance matrix of some Gaussian state is Σ + ½ iΩ ≥ 0. Furthermore, it corresponds to a pure Gaussian state if
det Σ = 4^{-n}"; App. A: "Given a valid Σ, it represents a pure Gaussian state if and only if det Σ = 4^{-n}."

For an `n`-mode Gaussian state `ρ = ρ(µ, Σ)`: `ρ` is a pure state (a rank-one projector) if and only if
`det Σ = (1/4)ⁿ`.

**Formalization Note.** "Valid Σ" is the hypothesis that `Σ` is the covariance of the Gaussian state `ρ`. -/
theorem pure_iff_det {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S) :
    IsPure ρ ↔ S.det = (1 / 4 : ℝ) ^ n := by sorry

end BosonicResources
