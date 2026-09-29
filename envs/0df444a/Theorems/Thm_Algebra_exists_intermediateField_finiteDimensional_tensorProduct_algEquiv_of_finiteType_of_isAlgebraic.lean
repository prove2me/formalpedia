-- Prove2me | Theorems.Thm_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
-- name    : Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6cbdde59-5710-5598-b9bf-4e962823ed98
-- title:
--   Finite type algebras descend to a finite subextension
-- statement:
--   Let $k$ (in universe $u$) and $K$ (in universe $v$) be fields with $K$ a $k$-algebra that is algebraic over $k$, and let $A$ (in universe $w$) be a commutative ring with a $K$-algebra structure that is of finite type over $K$. The assertion is the existence of an intermediate field $L$ of the extension $K/k$, together with the property that $L$ is finite dimensional as a $k$-vector space, of a type $A_0$ in the same universe $v$ as $K$, of a commutative ring structure on $A_0$, of an $L$-algebra structure on $A_0$ making $A_0$ of finite type over $L$, and of an isomorphism of $K$-algebras $K \otimes_L A_0 \cong A$, the existence of the isomorphism being recorded as the nonemptiness of the type of such isomorphisms. The $K$-algebra structure on the tensor product is the one coming from the left factor, $L$ acting on $K$ through the inclusion of the intermediate field.
--
--   This is the affine case of the standard descent statement that a scheme of finite type over an algebraic extension field is obtained by base change from a finite subextension (EGA IV, 8.8.2–8.9.1). It is used to prove the corresponding pullback statement for schemes, [`AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic`](thm.html#AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (A : Type w) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L A₀) (_ : Algebra.FiniteType L A₀),
      Nonempty ((K ⊗[L] A₀) ≃ₐ[K] A) := by sorry
