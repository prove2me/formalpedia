-- Prove2me | Theorems.Thm_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
-- name    : Bialgebra.exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/fdb7b263-0d16-5f60-b2e1-888af52ac7a8
-- title:
--   Surjectivity and a dimension count split C as A⊗_k A
-- statement:
--   Let $k$ be a field and let $A$ and $C$ be commutative rings carrying $k$-bialgebra structures, both finite-dimensional as $k$-modules. Let $\rho_0,\rho_1\colon A\to C$ be homomorphisms of $k$-bialgebras. Assume two things: first, that the algebra map $A\otimes_k A\to C$ obtained from the underlying $k$-algebra homomorphisms by `Algebra.TensorProduct.productMap`, namely $a\otimes a'\mapsto \rho_0(a)\,\rho_1(a')$, is surjective as a function; second, that $\dim_k C=\dim_k A\cdot\dim_k A$. Then there exists an isomorphism of $k$-bialgebras $\kappa\colon C\xrightarrow{\ \sim\ }A\otimes_k A$ such that its inverse satisfies $\kappa^{-1}(a\otimes 1)=\rho_0(a)$ and $\kappa^{-1}(1\otimes a)=\rho_1(a)$ for all $a\in A$, and indeed $\kappa^{-1}(x)$ equals the above product map evaluated at $x$ for every $x\in A\otimes_k A$. Thus the product map itself is a bialgebra isomorphism, with the two given homomorphisms recovered as its restrictions to the two tensor factors.
--
--   In the language of finite schemes this is the coordinate-ring form of the statement that a closed subscheme of $G\times G$ whose order equals that of $G\times G$ is the whole of $G\times G$: if $(r_0,r_1)\colon H\to G\times G$ is a closed immersion of finite group (or monoid) schemes and $H$ has order $(\#G)^2$, then it is an isomorphism. It is used in the construction of a bialgebra identification for the base change of a Raynaud quotient with a tensor square of level-torsion coordinate rings over a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
    (k : Type*) [Field k] (A C : Type*) [CommRing A] [CommRing C] [Bialgebra k A] [Bialgebra k C]
    [FiniteDimensional k A] [FiniteDimensional k C]
    (ρ₀ ρ₁ : A →ₐc[k] C)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C)))
    (hrank : Module.finrank k C = Module.finrank k A * Module.finrank k A) :
    ∃ κ : C ≃ₐc[k] A ⊗[k] A,
      (∀ a : A, κ.symm (a ⊗ₜ[k] 1) = ρ₀ a) ∧ (∀ a : A, κ.symm (1 ⊗ₜ[k] a) = ρ₁ a) ∧
      ∀ x : A ⊗[k] A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x := by sorry
