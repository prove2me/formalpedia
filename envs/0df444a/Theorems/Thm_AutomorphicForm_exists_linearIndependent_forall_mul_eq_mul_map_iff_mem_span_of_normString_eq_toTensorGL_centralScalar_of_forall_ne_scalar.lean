-- Prove2me | Theorems.Thm_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
-- name    : AutomorphicForm.exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d3c43e11-8768-5924-a968-d38299e1f039
-- title:
--   A K-basis for the twisted commutant of δ₀
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Let $\delta_0 \in GL_2(L)$, let $c$ be a unit of $L \otimes_K \mathbb{A}_K$ (where $\mathbb{A}_K$ is the adele ring of $\mathcal{O}_K$ in $K$) and let $u \in \mathbb{A}_K^\times$. Two hypotheses are imposed. First, writing $\delta$ for the product of the image of $\delta_0$ under the inclusion $L \to L \otimes_K \mathbb{A}_K$ of the left factor with the scalar matrix $c \cdot 1$, the norm string of $\delta$, namely the product $\prod_{i < \operatorname{finrank}_K L} \sigma_{GL}^{i}(\delta)$ over $i$ in $\{0, 1\}$ of the iterates of the entrywise automorphism induced by $\sigma$ on $GL_2(L \otimes_K \mathbb{A}_K)$, equals the image under $GL_2(\mathbb{A}_K) \to GL_2(L \otimes_K \mathbb{A}_K)$ (induced by $a \mapsto 1 \otimes a$) of the scalar matrix $u \cdot 1$. Second, $\delta_0$ is $\sigma$-twisted conjugate to no scalar: for all $x \in GL_2(L)$ and $z \in L^\times$ one has $x^{-1} \delta_0\, \sigma(x) \neq z \cdot 1$. The conclusion is that there exists $b : \{0,1,2,3\} \to M_2(L)$, linearly independent over $K$, such that for every $X \in M_2(L)$ the relation $X \delta_0 = \delta_0\, \sigma(X)$ (entrywise application of $\sigma$) holds if and only if $X$ lies in the $K$-span of the range of $b$.
--
--   The set $D_0 = \{X \in M_2(L) : X\delta_0 = \delta_0 \sigma(X)\}$ is the twisted commutant of $\delta_0$, and the statement exhibits it as a $K$-subspace of $M_2(L)$ of dimension $4 = 2[L:K]$ by producing an explicit $K$-basis indexed by four elements. It supplies the lattice datum used in the volume and covolume computations for twisted orbital integrals, being cited by [`AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex`](thm.html#AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex) and by [`AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact`](thm.html#AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
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
        Matrix.GeneralLinearGroup.scalar (Fin 2) z) :
    ∃ b : Fin 4 → Matrix (Fin 2) (Fin 2) L, LinearIndependent K b ∧
      ∀ X : Matrix (Fin 2) (Fin 2) L,
        X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
          X ∈ Submodule.span K (Set.range b) := by sorry
