-- Prove2me | Theorems.Thm_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
-- name    : AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/71dafa33-b127-551c-afd5-e008229ea242
-- title:
--   Bound on A[ℓ] from growth of τ^{ℓ^k}-fixed points
-- statement:
--   Let $A$ be an additive commutative group, let $\ell$ be a prime, let $r$ be a natural number and let $\tau : A \to A$ be an endomorphism of $A$ as an additive group; write $A\{\ell\} =$ `AddCommGroup.primaryComponent A ℓ` for the subgroup of elements of $\ell$-power order, and for $n$ a natural number let $\tau^{[n]}$ denote the $n$-fold iterate of the underlying map of $\tau$. Assume: (i) every $x \in A\{\ell\}$ satisfies $\tau^{[\ell^k]}(x) = x$ for some natural number $k$; (ii) there is a natural number $c$ such that for every natural number $k$ the set $\{x \in A\{\ell\} : \tau^{[\ell^k]}(x) = x\}$ is finite, of cardinality at most $\ell^{rk + c}$; (iii) every $x \in A\{\ell\}$ is divisible by $\ell$ in $A$, i.e. $x = \ell \cdot y$ for some $y \in A$. Then the $\ell$-torsion submodule of $A$ viewed as a $\mathbb{Z}$-module, `Submodule.torsionBy ℤ A (ℓ : ℤ)`, that is $A[\ell] = \{x \in A : \ell \cdot x = 0\}$, is finite and its cardinality is at most $\ell^{r}$.
--
--   This is the group-theoretic core of the upper-bound half of the classical determination of the $\ell$-primary torsion of a divisible group carrying an endomorphism whose fixed-point counts along the tower $\tau^{\ell^k}$ grow like $\ell^{rk}$: no $\ell$-adic rank larger than $r$ is compatible with such growth. It is applied, with $\tau$ a power of Frobenius and $A$ the degree-zero divisor class group of a curve over an algebraic closure of a finite field, in [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c))
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) :
    Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)) ∧
      Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r := by sorry
