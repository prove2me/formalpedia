-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
-- name    : AutomorphicForm.exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/812cd922-49f2-520f-9534-325714175210
-- title:
--   Archimedean column map bounded below on the twisted commutant
-- statement:
--   Let $K\subset L$ be number fields with $[L:K]=2$, let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, let $\delta_0\in \mathrm{GL}_2(L)$, and let $c$ be a unit of $L\otimes_K\mathbb{A}_K$ and $u$ a unit of $\mathbb{A}_K$, where $\mathbb{A}_K$ is the adele ring of $K$. Write $\delta=(\delta_0\otimes 1)\cdot c\!\cdot\!\mathrm{Id}$ for the product in $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ of the image of $\delta_0$ under $\ell\mapsto \ell\otimes 1$ with the scalar matrix of $c$. Assume (hN) that the norm string of $\delta$, i.e. the product $\prod_{i<[L:K]}(\sigma^{\otimes})^{i}(\delta)$ of the iterates of the entrywise map induced by $\sigma\otimes\mathrm{id}$ on $L\otimes_K\mathbb{A}_K$, equals the scalar matrix of $1\otimes u$; and (hns) that $x^{-1}\delta_0\,\sigma(x)$ is a scalar matrix for no $x\in\mathrm{GL}_2(L)$ and no $z\in L^\times$. Fix $v\in L^2$, $v\neq 0$. Equip $\mathbb{A}_{K,\infty}$ with the $\mathbb{R}$-algebra structure transported from the mixed space of $K$ along `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $L\otimes_K\mathbb{A}_{K,\infty}$ with the induced structure through $a\mapsto 1\otimes a$. Then for every $n_2$ and every $\mathbb{R}$-linearly independent family $e_2\colon \mathrm{Fin}\,n_2\to M_2(L\otimes_K\mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly $\{X : X\delta_\infty=\delta_\infty\,X^{\sigma\otimes\mathrm{id}}\}$, where $\delta_\infty$ is the image of $\delta$ under the map induced by $\mathrm{id}_L\otimes$ (projection of adeles to infinite adeles), there exists $\kappa>0$ such that for all $cc\in\mathbb{R}^{n_2}$, $\|cc\|\le \kappa\,\bigl\|\bigl(\iota_L(E_\infty(((\sum_k cc_k\,e_2(k))\cdot(v\otimes 1))_i))\bigr)_{i}\bigr\|$, with $E_\infty\colon L\otimes_K\mathbb{A}_{K,\infty}\to\mathbb{A}_{L,\infty}$ the archimedean base-change identification [`AutomorphicForm.archIdent`](def/AutomorphicForm_TwistedOrbital.html#L420) and $\iota_L$ the ring isomorphism of $\mathbb{A}_{L,\infty}$ with the mixed space of $L$.
--
--   The statement expresses that, under the non-scalarity hypothesis making the $\sigma$-twisted commutant of $\delta_0$ a quaternion division algebra over $K$, the real-linear column map $cc\mapsto(\sum_k cc_k e_2(k))\cdot v$ from a real frame of the archimedean twisted commutant into $(\mathbb{A}_{L,\infty})^2$ is injective, hence bounded below. It supplies the coercivity input for the convergence and limit estimates for twisted orbital integrals over the twisted centraliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ →
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
            ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
              X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
        ∃ κ : ℝ, 0 < κ ∧ ∀ cc : Fin n₂ → ℝ,
          ‖cc‖ ≤ κ * ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L
              (((∑ k, cc k • e₂ k).mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)))‖ := by sorry
