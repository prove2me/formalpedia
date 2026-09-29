-- Prove2me | Theorems.Thm_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable
-- name    : ArtinL.hasProd_inv_eval_eulerFactor_of_lSeriesSummable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/76ef2529-e0ac-5912-9050-bca021d1b26a
-- title:
--   Euler product for an Artin L-series at a point of summability
-- statement:
--   Let $n$ be a natural number and let $\rho$ be a monoid homomorphism from $\Gamma_{\mathbb Q} = \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_n(\mathbb C)$. For a natural number $p$ the local factor [`ArtinL.eulerFactor ρ p`](def/ArtinL_EulerFactor.html#L86) is the polynomial defined as follows: if there is a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ lying in the nonunits of $A$ and an automorphism $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ acting on the residue field of $A$ by $x \mapsto x^{p}$, then, for one such chosen pair $(A,\sigma)$, it is the reversed characteristic polynomial of the matrix of $\rho(\sigma)$ restricted to the inertia invariants of $\rho$ at $A$ when that subspace is preserved, and $1$ otherwise; if no such pair exists it is $1$. Write [`ArtinL.coeffPrimePow ρ p k`](def/ArtinL_EulerFactor.html#L92) for the $k$-th coefficient of the inverse of [`ArtinL.eulerFactor ρ p`](def/ArtinL_EulerFactor.html#L86) as a formal power series, and let [`ArtinL.coeff ρ`](def/ArtinL_EulerFactor.html#L95) be the arithmetic function vanishing at $0$ and sending $m \ge 1$ to the product of [`ArtinL.coeffPrimePow ρ p k`](def/ArtinL_EulerFactor.html#L92) over the prime powers $p^k$ in the factorisation of $m$. Fix $s \in \mathbb C$ and assume the Dirichlet series of [`ArtinL.coeff ρ`](def/ArtinL_EulerFactor.html#L95) is `LSeriesSummable` at $s$. Then: (i) for every prime $p$, the series $\sum_{k \ge 0}$ [`ArtinL.coeffPrimePow ρ p k`](def/ArtinL_EulerFactor.html#L92) $\cdot (p^{-s})^{k}$ has sum equal to the inverse of the value of [`ArtinL.eulerFactor ρ p`](def/ArtinL_EulerFactor.html#L86) at $p^{-s}$, and that value is nonzero; and (ii) the family of these inverses, indexed by the primes, has unconditional product equal to [`ArtinL.LSeries ρ s`](def/ArtinL_EulerFactor.html#L98), the value at $s$ of the Dirichlet series with coefficients [`ArtinL.coeff ρ`](def/ArtinL_EulerFactor.html#L95).
--
--   This is the Euler product of Artin's $L$-series, together with non-vanishing of the local factors, at any point in the region where the associated Dirichlet series is summable. It is used to upgrade a prime-by-prime identity between the local Euler factors of a representation and those of the abelian characters occurring in a Brauer decomposition of its character into the corresponding identity of $L$-series, as in [`ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.hasProd_inv_eval_eulerFactor_of_lSeriesSummable {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    {s : ℂ} (hsum : LSeriesSummable (ArtinL.coeff ρ) s) :
    (∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => ArtinL.coeffPrimePow ρ p k * ((p : ℂ) ^ (-s)) ^ k)
          (((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹) ∧
        (ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)) ≠ 0) ∧
    HasProd (fun p : Nat.Primes => ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.LSeries ρ s) := by sorry
