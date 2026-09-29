-- Prove2me | Theorems.Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
-- name    : Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/e8c535a3-cfa1-52eb-9213-4d0f97146570
-- title:
--   Integral closedness ascends to L ⊗_{k_0} S
-- statement:
--   Let $k_0$ be a field and let $S$ be a commutative ring which is an integrally closed domain equipped with a $k_0$-algebra structure; let $F$ be a field which is a $k_0$-algebra and an $S$-algebra, compatibly (the tower $k_0 \to S \to F$ is a scalar tower), and which is a fraction field of $S$, i.e. $F$ realises the localisation of $S$ at its non-zero divisors. Let $L$ be a field that is a finite-dimensional separable $k_0$-algebra, every element of $L$ being separable over $k_0$. All four types are taken in a single universe. Assume that the $F$-algebra $F \otimes_{k_0} L$ is a field. The conclusion is the conjunction of two assertions about the $k_0$-algebra $L \otimes_{k_0} S$: it is a domain (non-trivial, with no zero divisors), and it is integrally closed in the sense of Mathlib's `IsIntegrallyClosed`, i.e. every element of its fraction field that is integral over it lies in the image of $L \otimes_{k_0} S$. Note the order of the factors: the hypothesis concerns $F \otimes_{k_0} L$ while the conclusion concerns $L \otimes_{k_0} S$.
--
--   This is the classical statement that normality ascends along a finite separable base change of the constant field: if the generic fibre $F \otimes_{k_0} L$ stays a field, then $L \otimes_{k_0} S$ is again an integrally closed domain. It is used in the form for subalgebras, [`Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable`](thm.html#Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable), in the construction of models of modular curves and their coordinate rings over extensions of the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

theorem Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
    {k₀ S F L : Type u} [Field k₀] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra k₀ S]
    [Field F] [Algebra k₀ F] [Algebra S F] [IsScalarTower k₀ S F] [IsFractionRing S F]
    [Field L] [Algebra k₀ L] [FiniteDimensional k₀ L] [Algebra.IsSeparable k₀ L]
    (hF : IsField (F ⊗[k₀] L)) :
    IsDomain (L ⊗[k₀] S) ∧ IsIntegrallyClosed (L ⊗[k₀] S) := by sorry
