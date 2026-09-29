-- Prove2me | Theorems.Thm_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
-- name    : AutomorphicForm.linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/682bb44d-377c-591d-a5c0-5bde48c55217
-- title:
--   Archimedean twisted commutant as a real span of xᵢ⊗ωₐ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, let $\delta_0\in \mathrm{GL}_2(L)$, and let $c$ be a unit of $L\otimes_K \mathbb{A}_{K,\infty}$, where $\mathbb{A}_{K,\infty}$ is the infinite adele ring of $K$. Let $\kappa$ be a finite index type and $x:\kappa\to M_2(L)$ a $K$-linearly independent family such that, for every $X\in M_2(L)$, the relation $X\delta_0=\delta_0\,\sigma(X)$ (with $\sigma$ applied entrywise) holds if and only if $X$ lies in the $K$-span of the range of $x$; thus $x$ is a $K$-basis of the $\sigma$-twisted commutant of $\delta_0$. Both $\mathbb{A}_{K,\infty}$ and $L\otimes_K\mathbb{A}_{K,\infty}$ are given the $\mathbb{R}$-algebra structures obtained from the identification of $\mathbb{A}_{K,\infty}$ with the mixed space of $K$ and, for the tensor product, from the right inclusion $\mathbb{A}_{K,\infty}\to L\otimes_K\mathbb{A}_{K,\infty}$. The assertion is twofold. First, the family indexed by pairs $(a,i)$, with $a$ running over the chosen $\mathbb{Z}$-basis index set of $\mathcal{O}_K$ and $i\in\kappa$, whose $(a,i)$ member is the matrix obtained from $x_i$ by applying entrywise $l\mapsto l\otimes \omega_a$, where $\omega_a$ is the image in $\mathbb{A}_{K,\infty}$ of the $a$-th element of the integral basis of $K$, is $\mathbb{R}$-linearly independent. Second, the $\mathbb{R}$-span of this family, viewed as a subset of $M_2(L\otimes_K\mathbb{A}_{K,\infty})$, is exactly the set of $X$ with $X\delta=\delta\,(\sigma\otimes\mathrm{id})(X)$, where $\delta$ is the product of the image of $\delta_0$ under the entrywise map induced by $L\to L\otimes_K\mathbb{A}_{K,\infty}$, $l\mapsto l\otimes 1$, with the scalar matrix $c\cdot 1$, and $(\sigma\otimes\mathrm{id})$ is applied entrywise through the ring endomorphism [`AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ`](def/AutomorphicForm_TwistedOrbital.html#L199) of $L\otimes_K\mathbb{A}_{K,\infty}$ induced by $\sigma$ on the left factor and the identity on the right.
--
--   This identifies the archimedean twisted commutant of $\delta=(\delta_0\otimes 1)c$ over $L\otimes_K\mathbb{A}_{K,\infty}$ as the real span of the products of a $K$-basis of the twisted commutant over $L$ with an integral basis of $K$, together with the independence of that product family. It is the linear-algebra input for the archimedean normalisations of the twisted orbital integrals, and is used in the computations of the Gram determinant and of the Haar volume of the associated parallelepiped.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor.lean

import Definitions.Def_AutomorphicForm_TwistedCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    {κ : Type} [Fintype κ] (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    LinearIndependent ℝ (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1))) ∧
    (Submodule.span ℝ (Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1)))) :
        Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      {X | X * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} := by sorry
