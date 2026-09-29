-- Prove2me | Theorems.Thm_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight
-- name    : AutomorphicForm.isClosedEmbedding_unitsMap_includeRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/4d4e3ad9-edeb-5bad-8669-208755c3b071
-- title:
--   K_∞^× → (L⊗_K K_∞)^× is a closed embedding
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ given as a $K$-algebra that is finite-dimensional over $K$. Write $K_\infty =$ `InfiniteAdeleRing K` for the infinite adele ring of $K$, and form the tensor product $L \otimes_K K_\infty$, regarded as a $K_\infty$-module through the right-hand factor (the `TensorProduct.RightActions` conventions) and equipped with the resulting module topology, for which it is a topological ring. The $K$-algebra homomorphism `Algebra.TensorProduct.includeRight` is the map $a \mapsto 1 \otimes a$ from $K_\infty$ into $L \otimes_K K_\infty$; passing to its underlying monoid homomorphism and applying `Units.map` gives the induced homomorphism of unit groups $K_\infty^\times \to (L \otimes_K K_\infty)^\times$, $u \mapsto 1 \otimes u$. The assertion is that this map on unit groups is a closed embedding: it is a topological embedding (a homeomorphism onto its image, for the unit-group topologies) whose image is closed in $(L \otimes_K K_\infty)^\times$.
--
--   This identifies $K_\infty^\times$ with a closed subgroup of the unit group of the twisted torus $L \otimes_K K_\infty$, the archimedean local situation underlying the comparison of automorphic integrals over $(L \otimes_K K_\infty)^\times$ with integrals over $K_\infty^\times$. It is used in the measure-theoretic step [`AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq`](thm.html#AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isClosedEmbedding_unitsMap_includeRight
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Topology.IsClosedEmbedding ((Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) : (InfiniteAdeleRing K)ˣ → (L ⊗[K] InfiniteAdeleRing K)ˣ) := by sorry
