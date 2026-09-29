-- Prove2me | Theorems.Thm_AutomorphicForm_isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace
-- name    : AutomorphicForm.isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e40fc0ac-4d62-51a7-b2cf-80b4d78a2ead
-- title:
--   Non-zero elements of the local twisted commutant are units
-- statement:
--   Let $K \subset L$ be number fields with $[L:K]=2$, let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbf{A}_K$ and $u$ an idele class unit of $\mathbf{A}_K$, where $\mathbf{A}_K$ denotes the adele ring of $K$. Write $\delta$ for the product of the image of $\delta_0$ under $L \to L\otimes_K \mathbf{A}_K$, $x \mapsto x \otimes 1$, with the scalar matrix of $c$. Assume: (hN) the ordered product $\prod_{i<[L:K]} (\sigma\otimes 1)^i(\delta)$, taken entrywise on matrices, equals the scalar matrix of the image of $u$ under $a \mapsto 1 \otimes a$; (hns) for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ is $x^{-1}\delta_0\,\sigma(x)$ the scalar matrix of $z$. Fix a finite place $v$ of $K$, given by a height-one prime of $\mathcal{O}_K$, and let $\delta_v \in \mathrm{GL}_2(L\otimes_K K_v)$ be the image of $\delta$ under $\mathrm{id}_L \otimes (\mathbf{A}_K \to K_v)$. Further data: a Haar measure $\tau$ on the $\sigma$-twisted centraliser $\{t : t\,\delta_v\,((\sigma\otimes 1)t)^{-1} = \delta_v\}$ of $\delta_v$ in $\mathrm{GL}_2(L\otimes_K K_v)$; an element $tv \in [0,\infty]$; (hnsc) no scalar matrix of a unit of $L\otimes_K K_v$ is of the form $x^{-1}\delta_v\,(\sigma\otimes 1)(x)$; (hshell) the $\tau$-measure of the set of $t$ in that twisted centraliser whose determinant is $1 \otimes s$ for some $s \in K_v^\times$ of valuation $1$, multiplied by the absolute norm of $v$, equals $tv$ plus that same measure; and a finite family $b$ of matrices in $M_2(L)$ which is $K$-linearly independent and whose $K$-span is exactly $\{X \in M_2(L) : X\delta_0 = \delta_0\,\sigma(X)\}$. The conclusion: every non-zero $X \in M_2(L\otimes_K K_v)$ satisfying $X \delta_0 = \delta_0 \cdot (\sigma\otimes 1)(X)$, where $\delta_0$ is read in $\mathrm{GL}_2(L\otimes_K K_v)$ via $x \mapsto x\otimes 1$ (the central factor $c$ does not occur here), is a unit of the matrix ring.
--
--   This is the local division-algebra property of the twisted commutant at a place $v$ where the twisted conjugacy class of $\delta$ misses the scalars: the $K_v$-algebra cutting out the twisted centraliser has no non-trivial zero divisors. It is the input ensuring invertibility in the local covolume computations for twisted orbital integrals, and is used in the evaluation of the lattice integrals of $\lvert\det\rvert$ attached to such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
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

theorem AutomorphicForm.isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace
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
    (v : HeightOneSpectrum (𝓞 K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτ : τ.IsHaarMeasure) (tv : ℝ≥0∞)
    (hnsc : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (hshell : τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        tv +
          τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b)) :
    ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀),
      X ≠ 0 → IsUnit X := by sorry
