-- Prove2me | Theorems.Thm_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
-- name    : AutomorphicForm.unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b0550787-18dc-5067-ba76-034e39e8ce79
-- title:
--   σ⊗ 1-invariant units of L⊗_K K_∞ are 1⊗ K_∞^×
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ an algebra over $K$ that is finite-dimensional over $K$ and Galois over $K$. Let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$. Write $K_\infty$ for the infinite adele ring `InfiniteAdeleRing K` of $K$ and consider the tensor product $L \otimes_K K_\infty$, whose ring structure is used to form the unit group $(L \otimes_K K_\infty)^\times$. The ring endomorphism [`AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ`](def/AutomorphicForm_TwistedOrbital.html#L199) is the one induced by $\sigma$ on the left factor and the identity on $K_\infty$, i.e. $\sigma \otimes \mathrm{id}$. The assertion is that for a unit $s \in (L \otimes_K K_\infty)^\times$, the image of $s$ under the induced map of unit groups equals $s$ if and only if $s$ lies in the range of the map of unit groups induced by the $K$-algebra homomorphism $\mathrm{includeRight} : K_\infty \to L \otimes_K K_\infty$, $p \mapsto 1 \otimes p$; that is, the $\sigma \otimes \mathrm{id}$-fixed units are exactly those of the form $1 \otimes p$ with $p$ a unit of $K_\infty$.
--
--   This is the Galois-descent computation of the fixed points of $\sigma\otimes\mathrm{id}$ on the units of the base change $L\otimes_K K_\infty$, equivalently the kernel of the twisted difference map on that unit group. It is used in the analysis of twisted orbital integrals, where it identifies the fibres of the relevant quotient, and is cited by [`AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq`](thm.html#AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s = s ↔ s ∈ Set.range (Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) := by sorry
