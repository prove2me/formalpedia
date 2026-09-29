-- Prove2me | Theorems.Thm_ArtinL_LSeriesSummable_coeff_of_one_lt_re
-- name    : ArtinL.LSeriesSummable_coeff_of_one_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/86001b6c-75f5-51f1-b0af-7e336c8a4286
-- title:
--   Absolute convergence of Artin L-series for Re(s)>1
-- statement:
--   Fix $n \in \mathbb{N}$ and a monoid homomorphism $\rho$ from $\Gamma_{\mathbb Q} = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_n(\mathbb C)$. Assume $\rho$ satisfies [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17), that is: there is an intermediate field $L$ between $\mathbb Q$ and $\overline{\mathbb Q}$ which is finite-dimensional over $\mathbb Q$ and such that $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Let $s \in \mathbb C$ with $\mathrm{Re}(s) > 1$. The conclusion is that the Dirichlet series with coefficients [`ArtinL.coeff ρ`](def/ArtinL_EulerFactor.html#L95) is summable at $s$, i.e. the family $m \mapsto a(m)\,m^{-s}$ indexed by $m \in \mathbb{N}$ is summable, where $a(0) = 0$ and, for $m \geq 1$, $a(m)$ is the product over the prime factorisation of $m$ of the quantities [`ArtinL.coeffPrimePow ρ p k`](def/ArtinL_EulerFactor.html#L92) taken at the exponent $k$ of each prime $p$ dividing $m$; here [`ArtinL.coeffPrimePow ρ p k`](def/ArtinL_EulerFactor.html#L92) is the coefficient of $X^k$ in the inverse, as a formal power series over $\mathbb C$, of the local Euler factor `eulerFactor ρ p`. Since summability of a family over $\mathbb{N}$ in $\mathbb{C}$ is unconditional, this is absolute convergence of $L(\rho,s)$.
--
--   This is the classical convergence statement for Artin $L$-series of complex representations of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ with finite image: the Euler product, expanded as a Dirichlet series, converges absolutely in the half-plane $\mathrm{Re}(s) > 1$. It underlies the analytic manipulations of Artin $L$-series in this development, and is used in establishing the functional equation of the completed $L$-series for odd representations and in the identification of the $L$-series through its Frobenius traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_LSeriesSummable_coeff_of_one_lt_re.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.LSeriesSummable_coeff_of_one_lt_re {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.coeff ρ) s := by sorry
