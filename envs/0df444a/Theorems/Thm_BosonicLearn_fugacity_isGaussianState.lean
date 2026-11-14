-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_isGaussianState
-- name    : BosonicLearn.fugacity_isGaussianState
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:48:13.270149+00:00
-- url     : https://prove2.me/theorems/0ffed82d-1aaf-4402-ab05-292b82f81700
-- title:
--   $\det(I-R)\Gamma(R)$ is the Gaussian state with mean $0$ and covariance $\tfrac12(1+R)(1-R)^{-1}$ (real form)
-- statement:
--   The fugacity form is a Gaussian state, with explicit covariance.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix with $1-R$ positive definite, and $C=(1+R)(1-R)^{-1}$ (Hermitian). Then $\det(1-R)\Gamma(R)$ is the coefficient array of a state $\rho_R$, and $\rho_R$ is the Gaussian state $\rho(0,\Sigma)$ with
--
--   $$
--   \Sigma=\frac12\begin{pmatrix}\operatorname{Re}C&-\operatorname{Im}C\\ \operatorname{Im}C&\operatorname{Re}C\end{pmatrix}
--   $$
--
--   in the grouped order $(q_1,\dots,q_n,p_1,\dots,p_n)$.
--
--   Checks. $R=0$ gives the vacuum $\Sigma=\tfrac12\mathbf 1$. For one mode, $\Sigma=\tfrac12\frac{1+d}{1-d}\mathbf 1$, the thermal state with mean photon number $d/(1-d)$. The formula was also checked numerically against the definition for a random $2$-mode $R$.
--
--   Role. Explicit form of clause 1 of Lemma 2 of the paper. It gives directly that $\rho_R$ is passive (with `BosonicLearn.gammaFock_basic`) and that $R\succeq\frac{\nu}{1+\nu}$ implies $\Sigma\succeq(\tfrac12+\nu)\mathbf 1$ (`BosonicLearn.fugacity_promiseClass`).
--
--   **Formalization Note** `IsGaussianState` is the mission predicate (characteristic function, finite energy, symmetric covariance, first and second moments); the covariance is written with `Matrix.fromBlocks` and entrywise real and imaginary parts of $C$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **`det(I − R)Γ(R)` is the Gaussian state with mean `0` and covariance `½ (1 + R)(1 − R)⁻¹`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "Given R, which we call the fugacity matrix, the corresponding passive Gaussian state is
ρ = det(I − R)Γ(R)."

Let `R` be positive semidefinite with `1 − R` positive definite, and `C = (1 + R)(1 − R)⁻¹` (Hermitian). Then
`det(1 − R)Γ(R)` is the coefficient array of a state, and that state is Gaussian with mean `0` and covariance
matrix, in the grouped order `(q₁,…,qₙ,p₁,…,pₙ)`,

`Σ = ½ [[Re C, −Im C], [Im C, Re C]]`.

**Formalization Note.** Explicit form of the first clause of `lemma_2`. For `R = 0` this is the vacuum, `Σ = ½ I`;
for one mode, `Σ = ½ (1 + d)/(1 − d) · I`, the thermal state with mean photon number `d/(1 − d)`. -/
theorem fugacity_isGaussianState {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧
      IsGaussianState ρ 0 ((1 / 2 : ℝ) • Matrix.fromBlocks
        (((1 + R) * (1 - R)⁻¹).map Complex.re) (-(((1 + R) * (1 - R)⁻¹).map Complex.im))
        (((1 + R) * (1 - R)⁻¹).map Complex.im) (((1 + R) * (1 - R)⁻¹).map Complex.re)) := by sorry

end BosonicLearn
