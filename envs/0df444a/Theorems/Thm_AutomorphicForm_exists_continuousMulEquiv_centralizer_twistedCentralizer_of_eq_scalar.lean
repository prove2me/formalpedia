-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
-- name    : AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9d57e1e5-8d0d-5814-836f-817499b081c4
-- title:
--   Twisted centralizer of a σ-conjugate scalar is GL₂(A)
-- statement:
--   Let $L/K$ be a finite Galois extension of fields and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $K$-algebra automorphism $\theta$ of $L$ lies in the subgroup of integral powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$). Let $A$ be a commutative topological $K$-algebra whose ring operations are continuous, and topologise $L \otimes_K A$ by the right-action conventions for tensor products. Let $\gamma \in GL_2(A)$ and assume $\gamma = c \cdot 1$ for some unit $c \in A^\times$. Let $\delta, y \in GL_2(L \otimes_K A)$ and $\zeta \in (L \otimes_K A)^\times$ satisfy $y^{-1}\,\delta\,\sigma(y) = \zeta \cdot 1$, where $\sigma$ acts on $GL_2(L \otimes_K A)$ entrywise through the ring endomorphism $\sigma \otimes \mathrm{id}_A$ of $L \otimes_K A$. The assertion is the existence of an isomorphism of topological groups (a multiplicative equivalence that is simultaneously a homeomorphism) $e$ from the centralizer of the singleton $\{\gamma\}$ in $GL_2(A)$ onto the $\sigma$-twisted centralizer of $\delta$, namely the subgroup $\{t \in GL_2(L \otimes_K A) : t\,\delta\,\sigma(t)^{-1} = \delta\}$, which is moreover given by the explicit formula $e(s) = y \cdot (1 \otimes s) \cdot y^{-1}$, the element $1 \otimes s$ being the image of $s$ under the map $GL_2(A) \to GL_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$.
--
--   This is the computation, by Galois descent, of the twisted centralizer at a $\sigma$-conjugacy class whose norm is central: such a twisted centralizer is an inner form of $GL_2$ which is $GL_2$ of the ground algebra itself, as occurs in the comparison of twisted and ordinary orbital integrals for cyclic base change for $GL(2)$. It is used in the project's construction of twisted sections over the adele ring and in the volume computations for fundamental domains of twisted centralizers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A)) (ζ : (L ⊗[K] A)ˣ)
    (hζ : y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) :
    ∃ e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* AutomorphicForm.twistedCentralizer K L A σ δ,
      ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        ((e s : AutomorphicForm.twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
          y * AutomorphicForm.toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := by sorry
