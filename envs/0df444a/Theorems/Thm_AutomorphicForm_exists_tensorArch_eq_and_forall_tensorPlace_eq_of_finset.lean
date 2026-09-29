-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
-- name    : AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d6a0c58f-6090-56e5-b967-42cdef96dec5
-- title:
--   Prescribing finitely many local components of an adelic matrix
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $B$ be a finite set of nonzero prime ideals of the ring of integers $\mathcal{O}_K$, let $x_a \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, where $\mathbb{A}_{K,\infty}$ is the infinite adele ring of $K$, and for every nonzero prime $v$ of $\mathcal{O}_K$ let $x_v \in \mathrm{GL}_2(L \otimes_K K_v)$, with $K_v$ the $v$-adic completion. Then there is an invertible $2 \times 2$ matrix $x$ over $L \otimes_K \mathbb{A}_K$ such that: the image of $x$ under the entrywise map induced by the $K$-algebra homomorphism $\mathrm{id}_L \otimes \mathrm{pr}_\infty : L \otimes_K \mathbb{A}_K \to L \otimes_K \mathbb{A}_{K,\infty}$ (the map [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46)) equals $x_a$; for every $v \in B$ the image of $x$ under the entrywise map induced by $\mathrm{id}_L \otimes \mathrm{pr}_v : L \otimes_K \mathbb{A}_K \to L \otimes_K K_v$ (the map [`AutomorphicForm.tensorPlace`](def/AutomorphicForm_BaseChangePlaces.html#L49) at $v$) equals $x_v$; and for every $v \notin B$ that image is the identity matrix. Thus only the values of the family $(x_v)_v$ at the finitely many places in $B$ are prescribed.
--
--   This is the adelic gluing (strong approximation-free, purely restricted-product) statement that a family of local invertible matrices over the base-changed local factors, trivial outside a finite set of finite places and with arbitrary archimedean part, is realised by a single element of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. It is used in the reduction of twisted weighted orbital integrals of a base-changed automorphic form to products of local integrals, where local data at finitely many places must be assembled into a global adelic matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : Finset (HeightOneSpectrum (𝓞 K)))
    (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.tensorArch K L x = xa ∧
      (∀ v ∈ B, AutomorphicForm.tensorPlace K L v x = xv v) ∧
      (∀ v ∉ B, AutomorphicForm.tensorPlace K L v x = 1) := by sorry
