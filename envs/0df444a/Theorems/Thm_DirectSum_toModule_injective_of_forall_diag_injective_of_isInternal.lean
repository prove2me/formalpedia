-- Prove2me | Theorems.Thm_DirectSum_toModule_injective_of_forall_diag_injective_of_isInternal
-- name    : DirectSum.toModule_injective_of_forall_diag_injective_of_isInternal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/da9f01d9-b89a-54f0-98f0-e3bdd5ab3076
-- title:
--   Bidegreewise injectivity from injectivity on each anti-diagonal
-- statement:
--   Let $R$ be a commutative ring and $H'$ an $R$-module, and let $\mathcal{A}' : \mathbb{N} \to \operatorname{Submodule} R\,H'$ be a family of submodules which is an internal direct sum decomposition of $H'$ in the sense of `DirectSum.IsInternal`, i.e. the canonical map $\bigoplus_{n} \mathcal{A}'_n \to H'$ is bijective. Let $M : \mathbb{N} \times \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules indexed by pairs of natural numbers, and let $\Psi_{a,b} : M_{a,b} \to H'$ be $R$-linear maps such that $\Psi_{a,b}(x) \in \mathcal{A}'_{a+b}$ for all $(a,b)$ and all $x \in M_{a,b}$. Assume that for every $n \in \mathbb{N}$ the induced map out of the direct sum over the anti-diagonal [`DoubleComplex.Diag n`](def/AlgebraicGeometry_DoubleComplex.html#L34), the subtype of pairs $(p,q)$ with $p+q = n$, namely $\bigoplus_{p+q=n} M_{p,q} \to H'$ assembled from the maps $\Psi_{p,q}$, is injective. Then the map $\bigoplus_{(a,b) \in \mathbb{N}^2} M_{a,b} \to H'$ assembled from all the $\Psi_{a,b}$ is injective.
--
--   A piece of graded linear algebra: injectivity of a map out of a bigraded direct sum that respects an internal grading on the target can be tested one total degree at a time. It is used in the proof of Künneth-type injectivity for presheaves of modules, where $M_{a,b}$ is a tensor product of graded pieces and $\Psi_{a,b}$ is the product of two pullback maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DirectSum_toModule_injective_of_forall_diag_injective_of_isInternal.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped DirectSum

universe u

theorem DirectSum.toModule_injective_of_forall_diag_injective_of_isInternal
    {R : Type u} [CommRing R] {H' : Type u} [AddCommGroup H'] [Module R H']
    (𝒜' : ℕ → Submodule R H') (h𝒜' : DirectSum.IsInternal 𝒜')
    (M : ℕ × ℕ → Type u) [∀ ab, AddCommGroup (M ab)] [∀ ab, Module R (M ab)]
    (Ψ : ∀ ab : ℕ × ℕ, M ab →ₗ[R] H') (hΨ : ∀ (ab : ℕ × ℕ) (x : M ab), Ψ ab x ∈ 𝒜' (ab.1 + ab.2))
    (hinj : ∀ n : ℕ, Function.Injective (DirectSum.toModule R (DoubleComplex.Diag n) H' (fun i => Ψ i.1))) :
    Function.Injective (DirectSum.toModule R (ℕ × ℕ) H' Ψ) := by sorry
