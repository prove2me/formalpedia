-- Prove2me | Theorems.Thm_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
-- name    : AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b0628321-2cc0-5ac4-924b-5415aec13237
-- title:
--   ℓ-power torsion from fixed-point counts of an endomorphism
-- statement:
--   Let $A$ be an additive abelian group, $\ell$ a prime, $r$ a natural number and $\tau\colon A \to A$ an additive endomorphism. Write $A[m]$ for the $\mathbb{Z}$-torsion submodule $\{x \in A : m x = 0\}$ and $A\{\ell\}$ for the $\ell$-primary component of $A$, i.e. the subgroup of elements of $\ell$-power order. Assume: $A[\ell]$ is finite; $\#A[\ell] \le \ell^{r}$; $\tau$ fixes every $x$ with $\ell^{2} x = 0$, that is $\tau$ acts as the identity on $A[\ell^{2}]$; and there exist natural numbers $c$ and $k_0$ such that for every $k$ the set of $x \in A\{\ell\}$ with $\tau^{\ell^{k_0+k}}(x) = x$ (the $\ell^{k_0+k}$-fold iterate of $\tau$) has cardinality exactly $\ell^{rk+c}$; since `Nat.card` is $0$ on infinite types, this last hypothesis in particular forces each of these fixed-point sets to be finite. The conclusion is that for every natural number $n$ the group $A[\ell^{n}]$ has cardinality exactly $\ell^{rn}$; again finiteness is part of the assertion only in so far as `Nat.card` records it, the value $\ell^{rn}$ being nonzero.
--
--   This is the purely group-theoretic mechanism that converts exact growth $\ell^{rk+c}$ of fixed-point counts along the $\ell$-power iterates of an endomorphism into the statement that the $\ell^{n}$-torsion has order $\ell^{rn}$ for all $n$, so that the $\ell$-primary part is $(\mathbb{Q}_\ell/\mathbb{Z}_\ell)^{r}$. It is applied, with $A$ the degree-zero divisor class group of a curve over an algebraically closed field and $\tau$ a power of Frobenius acting trivially on $A[\ell^{2}]$, in [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic), where the fixed-point counts come from class numbers of the constant field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hfin : Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)))
    (hle : Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r)
    (hτ : ∀ x : A, ℓ ^ 2 • x = 0 → τ x = x)
    (hfix : ∃ c k₀ : ℕ, ∀ k : ℕ,
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₀ + k)] x = x} =
        ℓ ^ (r * k + c))
    (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)) = ℓ ^ (r * n) := by sorry
