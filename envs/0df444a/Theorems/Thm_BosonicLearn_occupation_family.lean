-- Prove2me | Theorems.Thm_BosonicLearn_occupation_family
-- name    : BosonicLearn.occupation_family
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:09:34.10919+00:00
-- url     : https://prove2.me/theorems/08d67d1b-e478-4f13-bd56-d70a0fd0d700
-- title:
--   The hard family for hot states: occupation matrices $N_X=m(1+\xi X)$ give passive Gaussian states of the promise class with Rényi-2 overlap $\le e^{21\xi^2n}$
-- statement:
--   The ensemble used for Theorem 9, parametrized so that the occupation matrix (not the fugacity matrix) is linear in $X$; all bounds are uniform in the temperature scale $m$.
--
--   Let $X$ be a Hermitian $n\times n$ matrix with $-4\cdot\mathbf 1\preceq X\preceq4\cdot\mathbf 1$, $m\ge1$, $0<\xi\le\frac1{32}$, $N=m(\mathbf 1+\xi X)$, $R=N(\mathbf 1+N)^{-1}$ and $r_0=\frac{m}{1+m}$. Then
--
--   1. $\frac78m\,\mathbf 1\preceq N\preceq\frac98m\,\mathbf 1$, $R\succeq0$, $\mathbf 1-R\succ0$ and $R^2\prec r_0\mathbf 1$;
--   2. for every $0<\nu\le\frac78m$ there is a density operator with Fock coefficients $\rho_R=\det(\mathbf 1-R)\Gamma(R)$ which is a passive Gaussian state with $\Sigma\succeq(\frac12+\nu)\mathbf 1$;
--   3. $\displaystyle\frac{\det(\mathbf 1-R)^2}{(1-r_0)^n\det(\mathbf 1-R^2/r_0)}\le e^{21\xi^2n}$.
--
--   The quantity in 3 is $\operatorname{Tr}(\rho_R\sigma^{-1/2}\rho_R\sigma^{-1/2})$ for the thermal state $\sigma$ of fugacity $r_0$ (see `BosonicLearn.fugacity_renyi2_tensorPow`); in an eigenbasis of $X$ it is $\prod_i\big(1+\frac{m^2\xi^2x_i^2}{m+2mN_i-N_i^2}\big)$.
--
--   **Formalization Note** $N$ and $R$ are introduced by equations `Nm = …`, `R = Nm * (1 + Nm)⁻¹`. The determinants are positive reals; their real parts are used.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §8, proof of Theorem 9, pp. 65–67 (Eq. (222): the ensemble of passive Gaussian states with $\Sigma\succeq(\frac12+\nu)I$); parametrization of §5.1, Eqs. (30)–(31), p. 30

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicLearn_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **The hard family for hot states: occupation matrices `N_X = m(1 + ξX)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §8, proof of Theorem 9, Eq. (222), p. 65 (the ensemble `ρ_U` of passive Gaussian states with `Σ ⪰ (½ + ν)I`), in the
parametrization of §5.1, Eqs. (30)–(31), p. 30, with the occupation matrix (rather than the fugacity matrix) linear in `X`.

Let `X` be Hermitian with `−4·1 ⪯ X ⪯ 4·1`, `m ≥ 1`, `0 < ξ ≤ 1/32`, `N = m(1 + ξX)` and `R = N(1 + N)⁻¹`. Then
1. `(7/8)m·1 ⪯ N ⪯ (9/8)m·1`, `0 ⪯ R`, `1 − R` is positive definite, and `R² ≺ r₀·1` for `r₀ = m/(1 + m)`;
2. for every `0 < ν ≤ (7/8)m` there is a state with Fock coefficients `ρ_R = det(1 − R)Γ(R)` which is a passive Gaussian
   state of the promise class `Σ ⪰ (½ + ν)I`;
3. the Rényi-2 overlap with the thermal state of fugacity `r₀` satisfies
   `det(1 − R)² / ((1 − r₀)ⁿ det(1 − R²/r₀)) ≤ exp(21 ξ² n)`.

**Formalization Note.** In an eigenbasis of `X` with eigenvalues `x_i`, `N_i = m(1 + ξx_i)` and the quantity in 3 is
`∏ᵢ (1 + m²ξ²x_i²/(m + 2mN_i − N_i²)) ≤ ∏ᵢ (1 + (64/49)ξ²x_i²)`. Real parts of the (positive real) determinants are used. -/
theorem occupation_family {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h4 : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef)
    (h4' : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef)
    (m ξ : ℝ) (hm : 1 ≤ m) (hξ0 : 0 < ξ) (hξ : ξ ≤ 1 / 32)
    (Nm R : Matrix (Fin n) (Fin n) ℂ)
    (hN : Nm = ((m : ℝ) : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + ((ξ : ℝ) : ℂ) • X))
    (hRdef : R = Nm * (1 + Nm)⁻¹) :
    (Nm - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
    (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Nm).PosSemidef ∧
    R.PosSemidef ∧ (1 - R).PosDef ∧
    (((m / (1 + m) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 7 / 8 * m →
      ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧ IsPassive ρ ∧
        ρ ∈ promiseClass n ν) ∧
    (1 - R).det.re ^ 2 /
        ((1 - m / (1 + m)) ^ n * (1 - (((m / (1 + m))⁻¹ : ℝ) : ℂ) • (R * R)).det.re) ≤
      Real.exp (21 * ξ ^ 2 * n) := by sorry

end BosonicLearn
