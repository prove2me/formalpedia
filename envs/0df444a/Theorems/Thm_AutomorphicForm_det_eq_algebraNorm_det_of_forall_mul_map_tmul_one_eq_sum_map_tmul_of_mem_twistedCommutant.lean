-- Prove2me | Theorems.Thm_AutomorphicForm_det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant
-- name    : AutomorphicForm.det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c192e2dc-1502-5c1b-8587-3e44c503c68a
-- title:
--   Determinant of left multiplication on the local twisted commutant
-- statement:
--   Let $K\subset L$ be number fields with $[L:K]=2$ and let $\sigma$ be a $K$-algebra automorphism of $L$ whose integer powers exhaust $\mathrm{Aut}_K(L)$. Let $\delta_0\in GL_2(L)$, $c\in (L\otimes_K\mathbb{A}_K)^\times$ and $u\in\mathbb{A}_K^\times$, and write $\delta=(\delta_0\otimes 1)\cdot c\,\mathrm{Id}$ for the image of $\delta_0$ under $l\mapsto l\otimes 1$ times the scalar matrix $c$. Assume (hN) the norm string of $\delta$, that is the product $\delta\cdot\sigma(\delta)$ of the $\mathrm{finrank}_K L = 2$ successive $\sigma$-twists of $\delta$, equals the scalar matrix with entry $1\otimes u$; and (hns) $x^{-1}\delta_0\,\sigma(x)$ is never a scalar matrix $z\,\mathrm{Id}$ for $x\in GL_2(L)$, $z\in L^\times$. Let $v$ be a height-one prime of $\mathcal{O}_K$, with completion $K_v$. Let $\iota$ be a finite type and $b:\iota\to M_2(L)$ a $K$-linearly independent family whose $K$-span is exactly $\{X\in M_2(L)\mid X\delta_0=\delta_0\,X^\sigma\}$. Let $X\in M_2(L\otimes_K K_v)$ satisfy $X\delta_v=\delta_v\,X^{\sigma\otimes 1}$, where $\delta_v$ is the image of $\delta$ under $L\otimes_K\mathbb{A}_K\to L\otimes_K K_v$, and let $P\in M_\iota(K_v)$ be such that $X\cdot(b_j\otimes 1)=\sum_i b_i\otimes P_{ij}$ for all $j$. Then $\det P$ equals the $K_v$-algebra norm of $\det X\in L\otimes_K K_v$.
--
--   This is the standard identification of the determinant of left multiplication by an element of the twisted commutant, viewed as a $K_v$-linear endomorphism in the coordinates given by the basis $b$, with the norm from $L\otimes_K K_v$ to $K_v$ of its reduced determinant. It is the algebraic ingredient in the comparison of additive and multiplicative Haar measures on the local twisted centraliser used by [`AutomorphicForm.setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure`](thm.html#AutomorphicForm.setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant

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

theorem AutomorphicForm.det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant
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
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (P : Matrix ι ι (v.adicCompletion K))
    (hP : ∀ j : ι, X * (b j).map (fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K)) =
      ∑ i : ι, (b i).map (fun l : L => l ⊗ₜ[K] P i j)) :
    P.det = Algebra.norm (v.adicCompletion K) (Matrix.det X) := by sorry
