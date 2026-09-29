-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/dd59a4de-4bff-5799-ad87-a01382dc5269
-- title:
--   Properness of the twisted orbit map modulo the twisted centralizer
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so $\sigma$ generates the Galois group). Write $\mathbb{A}_K$ for the adele ring of $K$ and let $\sigma$ act on $L \otimes_K \mathbb{A}_K$ as $\sigma \otimes \mathrm{id}$, inducing the entrywise map [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) on $G' = \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. Let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbb{A}_K$ and $u$ a unit of $\mathbb{A}_K$, and set $\delta = \delta_0^{\otimes} \cdot c \cdot 1$, where $\delta_0^{\otimes}$ is the image of $\delta_0$ under the entrywise map induced by $\ell \mapsto \ell \otimes 1$ and $c \cdot 1$ is the scalar matrix with entry $c$. Assume: the norm string of $\delta$, namely the product $\delta \cdot \sigma(\delta)$ of the $\operatorname{finrank}_K L = 2$ iterates $\sigma^i(\delta)$, equals the image of the scalar matrix $\mathrm{diag}(u,u) \in \mathrm{GL}_2(\mathbb{A}_K)$ under the entrywise map induced by $a \mapsto 1 \otimes a$; and $\delta_0$ is $\sigma$-conjugate over $L$ to no scalar matrix, i.e. $x^{-1} \delta_0 \sigma(x) \neq \mathrm{diag}(z,z)$ for all $x \in \mathrm{GL}_2(L)$ and $z \in L^{\times}$. Then for every compact $C \subseteq G'$ there is a compact $D \subseteq G'$ such that $\{x \in G' : x^{-1} \delta\, \sigma(x) \in C\} \subseteq T' \cdot D$, where $T' = \{t \in G' : t \delta \sigma(t)^{-1} = \delta\}$ is the $\sigma$-twisted centralizer of $\delta$.
--
--   This is the properness, modulo the twisted centralizer, of the $\sigma$-twisted orbit map $x \mapsto x^{-1}\delta\sigma(x)$ at an adelic class with central norm which is of the second kind (no scalar lies in the $\sigma$-conjugacy class of $\delta_0$ over $L$), as in Langlands' treatment of quadratic base change for $\mathrm{GL}(2)$. It is the convergence input for the computation of the corresponding adelic twisted orbital integral, which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
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
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ *
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
            AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by sorry
