-- Prove2me | Theorems.Thm_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
-- name    : AutomorphicForm.exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/ce9dc5fd-d47e-5f94-88ac-c9a4b71f5a70
-- title:
--   Adelic twisted centralizer element with prescribed components on S
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $2$ ($\mathrm{finrank}_K L=2$), let $\sigma$ be a $K$-algebra automorphism of $L$, let $\delta_0\in GL_2(L)$ and let $c$ be a unit of $L\otimes_K\mathbb{A}_K$, where $\mathbb{A}_K$ is the adele ring of $K$; write $\delta$ for the product of the image of $\delta_0$ under $GL_2$ of the inclusion $L\to L\otimes_K\mathbb{A}_K$ with the scalar matrix $c$. Let $\iota$ be a finite type and $b:\iota\to M_2(L)$ a $K$-linearly independent family such that, for every $X\in M_2(L)$, $X\delta_0=\delta_0\,X^{\sigma}$ holds precisely when $X$ lies in the $K$-span of the range of $b$; let $\beta:\iota\to K$ satisfy $\sum_k\beta_k b_k=1$. Let $S$ be a finite set of height-one primes of $\mathcal{O}_K$ and let $a:\iota\to\mathbb{A}_K$ be a family of adeles whose infinite components are the images of the $\beta_k$, whose components at each $w\notin S$ are the images of the $\beta_k$ in $K_w$, and such that for every $w\in S$ the matrix $\sum_k (b_k)\otimes a_{k,w}$ over $L\otimes_K K_w$ is the matrix of an element of the twisted centralizer at $w$, namely of $\{t: t\,\delta_w\,(\mathrm{sigmaGL}\,t)^{-1}=\delta_w\}$ in $GL_2(L\otimes_K K_w)$, with $\delta_w$ the image of $\delta$ under `tensorPlace` at $w$ (base change along $\mathbb{A}_K\to K_w$) and $\mathrm{sigmaGL}$ the endomorphism of $GL_2$ induced by the ring endomorphism `sigmaTensor` of $L\otimes_K K_w$ attached to $\sigma$. Then there is an element $t$ of the corresponding twisted centralizer $\{t: t\,\delta\,(\mathrm{sigmaGL}\,t)^{-1}=\delta\}$ in $GL_2(L\otimes_K\mathbb{A}_K)$ whose matrix is $\sum_k (b_k)\otimes a_k$ and whose image under `tensorPlace` at $w$ is the identity for every $w\notin S$.
--
--   This assembles local data on a twisted torus into a global adelic point: given coordinates, with respect to a rational basis of the twisted commutant of $\delta_0$, that are centralizer coordinates above each place of a finite set $S$ and the coordinates of the identity elsewhere, the resulting adelic matrix lies in the $\sigma$-twisted centralizer and is trivial outside $S$. It is used in the computation of measures of twisted-orbital integrals over products of local boxes, in the comparison of base-change Hecke eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (β : ι → K) (hβ : ∑ k, β k • b k = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → AdeleRing (𝓞 K) K)
    (harch : ∀ k, (a k).1 = algebraMap K (InfiniteAdeleRing K) (β k))
    (hS : ∀ w ∈ S, ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] (a k).2 w)
    (hoff : ∀ k, ∀ w ∉ S, (a k).2 w = algebraMap K (w.adicCompletion K) (β k)) :
    ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ((t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
          (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k) ∧
      ∀ w ∉ S, AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) = 1 := by sorry
