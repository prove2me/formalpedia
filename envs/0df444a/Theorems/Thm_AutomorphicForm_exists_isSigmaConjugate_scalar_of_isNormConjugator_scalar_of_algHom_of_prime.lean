-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
-- name    : AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f6084066-9d17-591a-b1d4-cf79b37db59a
-- title:
--   Norm conjugate to a scalar implies σ-conjugate to a scalar
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a finite-dimensional $K$-algebra whose degree $n = \dim_K L$ is a prime number, and let $\sigma : L \to L$ be a $K$-algebra automorphism with $\sigma \neq 1$. Let $A$ be a commutative $K$-algebra admitting a $K$-algebra homomorphism $\iota : L \to A$ (the split situation), let $c$ be a unit of $A$, and let $\delta, y \in \mathrm{GL}_2(L \otimes_K A)$. Write $\sigma$ also for the automorphism of $L \otimes_K A$ acting through the left factor and for the induced entrywise automorphism of $\mathrm{GL}_2(L \otimes_K A)$. Assume `IsNormConjugator` holds for the scalar matrix $c \cdot 1 \in \mathrm{GL}_2(A)$, $\delta$ and $y$, that is, the image of $c \cdot 1$ under the map $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$ equals $y^{-1} \, N(\delta) \, y$, where $N(\delta) = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ is the product of the first $n$ iterated $\sigma$-twists of $\delta$. Then there exist a unit $z$ of $L \otimes_K A$ and an $x \in \mathrm{GL}_2(L \otimes_K A)$ with $z \cdot 1 = x^{-1} \, \delta \, \sigma(x)$, i.e. $\delta$ is $\sigma$-twisted conjugate to a scalar matrix.
--
--   This is the split half of the local twisted-conjugacy analysis underlying base change for $\mathrm{GL}(2)$: at a place of $K$ that splits completely in the cyclic extension $L/K$ of prime degree, an element whose norm string is conjugate to a scalar is itself twisted conjugate to a scalar. It is used in the computation of twisted orbital integrals at scalar elements and in the construction of twisted section functions in the degree-two case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] (ι : L →ₐ[K] A)
    (c : Aˣ) (δ y : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ z : (L ⊗[K] A)ˣ,
      AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by sorry
