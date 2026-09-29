-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
-- name    : AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/fb96d15d-bcd1-5198-abf1-97cfc4e2c7c3
-- title:
--   Split regular diagonal is a σ-norm iff both entries are norms
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $A$ be a commutative $K$-algebra, and let $x, y \in A^{\times}$ be units whose difference $x - y$ is again a unit of $A$. Write $\mathrm{diagUnits2}\,x\,y$ for the element of $\mathrm{GL}_2(A)$ given by the matrix $\mathrm{diag}(x,y)$, with inverse $\mathrm{diag}(x^{-1},y^{-1})$. The assertion is an equivalence. On one side: there exists $\delta \in \mathrm{GL}_2(L \otimes_K A)$ for which $\mathrm{diag}(x,y)$ is a norm of $\delta$ in the sense of [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217), i.e. there is $t \in \mathrm{GL}_2(L \otimes_K A)$ with the image of $\mathrm{diag}(x,y)$ under `toTensorGL K L A` equal to $t^{-1} \cdot (\mathrm{normString}\ K\ L\ A\ \sigma\ \delta) \cdot t$. On the other side: both $x$ and $y$, viewed in $A$, lie in the image of the map sending a unit $t$ of $L \otimes_K A$ to $\mathrm{Algebra.norm}_A(t) \in A$.
--
--   This is the local bridge between the twisted (norm) conjugacy condition on $\mathrm{GL}_2$ over $L \otimes_K A$ for a cyclic extension $L/K$ and the plain condition that the diagonal entries be norms from $(L \otimes_K A)^{\times}$; the regularity hypothesis that $x - y$ be a unit is what forces a lift to be diagonal. It is used in the construction of twisted torus families and in the production of elements that fail to be norms, via [`AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct`](thm.html#AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct) and the two `exists_finset_not_isNormOf_and_not_card_eq_one` results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (x y : Aˣ) (hxy : IsUnit ((x : A) - (y : A))) :
    (∃ δ : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormOf K L A σ (diagUnits2 x y) δ) ↔
      ((x : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) ∧
       (y : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) := by sorry
