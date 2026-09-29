-- Prove2me | Theorems.Thm_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
-- name    : Algebra.TensorProduct.exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/9b5511aa-be57-592b-988e-56bb42d1356f
-- title:
--   A second branch through every zero of v
-- statement:
--   Let $R$ be a commutative ring and $\pi \in R$ an element whose principal ideal $(\pi)$ is maximal. Let $\mathcal{O}$ be a commutative $R$-algebra in which the image of $\pi$ is a non-zero-divisor, and let $\kappa$ be a field that is an $R$-algebra in which the image of $\pi$ is $0$; assume that the ring $\kappa \otimes_R \mathcal{O}$ is reduced. Let $v, v' \in \mathcal{O}$ and $n \in \mathbb{N}$ satisfy $v v' = (\text{image of } \pi)^n$ in $\mathcal{O}$. Let $Q_0$ and $\mathfrak{q}$ be ideals of $\kappa \otimes_R \mathcal{O}$ with $Q_0$ a minimal prime of the ring (a minimal element of the primes containing the zero ideal), $\mathfrak{q}$ prime, and $Q_0 \subseteq \mathfrak{q}$; assume $1 \otimes v \notin Q_0$ while $1 \otimes v \in \mathfrak{q}$. Then there exists a minimal prime $Q_1$ of $\kappa \otimes_R \mathcal{O}$ with $Q_1 \neq Q_0$ and $Q_1 \subseteq \mathfrak{q}$.
--
--   A statement of pure commutative algebra, phrased for an abstract base $(R,\pi)$: a factorisation $v v' = \pi^n$ upstairs, with $\pi$ regular on $\mathcal{O}$, forces a second irreducible component of the reduced special fibre $\operatorname{Spec}(\kappa \otimes_R \mathcal{O})$ to pass through every prime $\mathfrak{q}$ at which $v$ vanishes but which lies on a component where $v$ does not vanish identically. It is used in the analysis of supersingular points on the special fibre of modular curves, by [`ModularCurve.IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd`](thm.html#ModularCurve.IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd) and [`ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH`](thm.html#ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
    (R : Type*) [CommRing R] (π : R) (hπ : (Ideal.span {π}).IsMaximal)
    (𝒪 : Type*) [CommRing 𝒪] [Algebra R 𝒪] (hπ𝒪 : algebraMap R 𝒪 π ∈ nonZeroDivisors 𝒪)
    (κ : Type*) [Field κ] [Algebra R κ] (hπκ : algebraMap R κ π = 0)
    [IsReduced (κ ⊗[R] 𝒪)]
    (v v' : 𝒪) (n : ℕ) (hvv' : v * v' = algebraMap R 𝒪 π ^ n)
    (Q₀ 𝔮 : Ideal (κ ⊗[R] 𝒪)) (hQ₀ : Q₀ ∈ minimalPrimes (κ ⊗[R] 𝒪)) [𝔮.IsPrime] (hle : Q₀ ≤ 𝔮)
    (hv₀ : (1 : κ) ⊗ₜ[R] v ∉ Q₀) (hv : (1 : κ) ⊗ₜ[R] v ∈ 𝔮) :
    ∃ Q₁ ∈ minimalPrimes (κ ⊗[R] 𝒪), Q₁ ≠ Q₀ ∧ Q₁ ≤ 𝔮 := by sorry
