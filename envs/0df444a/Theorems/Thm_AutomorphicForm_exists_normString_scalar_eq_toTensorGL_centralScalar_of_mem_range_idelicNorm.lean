-- Prove2me | Theorems.Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm
-- name    : AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c22559cf-219e-520e-b39e-cca1a34cbb47
-- title:
--   Idelic norms are norm strings of adelic scalar matrices
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$). Let $u$ be a unit of the adele ring $\mathbb{A}_K$ of $K$, and assume that $u$ lies in the image of the idelic norm attached to the base-change datum [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), that is, the map $\mathbb{A}_L^{\times} \to \mathbb{A}_K^{\times}$ obtained by applying `Units.map` to the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$ for the $\mathbb{A}_K$-algebra structure on $\mathbb{A}_L$ given by the ring homomorphism `genuineβ K L` (the datum also records the $\mathbb{A}_K$-algebra isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ carrying $1 \otimes l$ to the image of $l$). Then there is a unit $c$ of $L \otimes_K \mathbb{A}_K$ such that the norm string of the scalar matrix $\mathrm{diag}(c,c) \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ relative to $\sigma$ — the ordered product over $i = 0, \dots, [L:K]-1$ of the $i$-fold iterates of the map induced on $\mathrm{GL}_2$ by $\sigma \otimes \mathrm{id}$, applied to $\mathrm{diag}(c,c)$ — equals the image of the central scalar matrix $\mathrm{diag}(u,u) \in \mathrm{GL}_2(\mathbb{A}_K)$ under the map induced on $\mathrm{GL}_2$ by $a \mapsto 1 \otimes a$.
--
--   This is the surjectivity half of the central-character bookkeeping in cyclic base change for $\mathrm{GL}(2)$: a central parameter of $\mathrm{GL}_2(\mathbb{A}_K)$ that is an idelic norm is realised as the twisted norm of a central element on the $L$-side. It is used in the comparison of the elliptic terms, where the central parameters are summed over the idelic norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct

theorem AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : u ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) :
    ∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) := by sorry
