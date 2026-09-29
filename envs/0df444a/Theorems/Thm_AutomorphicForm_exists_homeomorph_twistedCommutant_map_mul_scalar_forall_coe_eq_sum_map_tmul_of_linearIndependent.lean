-- Prove2me | Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
-- name    : AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/78b5ba74-1e37-53b7-9795-956b38d343a4
-- title:
--   Base change of the twisted commutant of δ₀⊗ 1
-- statement:
--   Let $L/K$ be an extension of fields with $L$ finite-dimensional over $K$, let $A$ be a commutative $K$-algebra carrying a topology making it a topological ring, let $\sigma$ be a $K$-algebra automorphism of $L$, let $\delta_0\in\mathrm{GL}_2(L)$, and let $c$ be a unit of $L\otimes_K A$. Let $\iota$ be a finite index type and $b\colon\iota\to M_2(L)$ a $K$-linearly independent family of matrices such that, for every $x\in M_2(L)$, the relation $x\delta_0=\delta_0\,(\sigma x)$ (with $\sigma$ applied entrywise) holds if and only if $x$ lies in the $K$-span of the range of $b$; thus $b$ is a $K$-basis of the $\sigma$-twisted commutant of $\delta_0$ in $M_2(L)$. Write $\delta$ for the product in $\mathrm{GL}_2(L\otimes_K A)$ of the image of $\delta_0$ under the entrywise map induced by $l\mapsto l\otimes 1$ with the scalar matrix $c\cdot 1$. The assertion is that there is a homeomorphism $e$ from $\iota\to A$, with the product topology, onto the subalgebra $\{X\in M_2(L\otimes_K A)\mid X\delta=\delta\,(\sigma\otimes\mathrm{id}_A)(X)\}$ of $M_2(L\otimes_K A)$, with its subspace topology, such that for every $a\colon\iota\to A$ the underlying matrix of $e(a)$ is $\sum_i (b_i)$ with each entry $l$ replaced by $l\otimes a_i$.
--
--   This is the extension-of-scalars (base change) description of the $\sigma$-twisted commutant: the central unit $c$ drops out of the defining relation, and the solution space over $A$ of the $K$-linear system $x\delta_0=\delta_0\,(\sigma x)$ is the free $A$-module obtained from the solution space over $K$ by tensoring, topologised as $A^{\iota}$. It supplies the coordinates used in the twisted orbital integral computations, including the volume and compactness statements for centralisers that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent.lean

import Definitions.Def_AutomorphicForm_TwistedCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hspan : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
        x ∈ Submodule.span K (Set.range b)) :
    ∃ e : (ι → A) ≃ₜ ↥(AutomorphicForm.twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ∀ a : ι → A,
        ((e a : AutomorphicForm.twistedCommutant K L A σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i := by sorry
