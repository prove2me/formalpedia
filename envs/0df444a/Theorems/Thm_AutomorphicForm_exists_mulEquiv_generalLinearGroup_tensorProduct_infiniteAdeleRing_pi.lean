-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
-- name    : AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/742fb65b-a5b6-5eb6-9f46-ef5041651b79
-- title:
--   GL₂(L⊗_K K_∞) splits over the infinite places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\Xi$ be a ring isomorphism from $L \otimes_K \mathbb{A}_{K,\infty}$, the base change to $L$ of the infinite adele ring of $K$, onto the product $\prod_{v} L \otimes_K K_v$ over the infinite places $v$ of $K$ of the base changes to $L$ of the completions, such that $\Xi$ and $\Xi^{-1}$ are continuous and $\Xi(x \otimes a)_v = x \otimes a_v$ for all $x \in L$, $a \in \mathbb{A}_{K,\infty}$ and all $v$. The assertion is that there exists a group isomorphism $\Theta : \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty}) \to \prod_v \mathrm{GL}_2(L \otimes_K K_v)$ with the following four properties: $\Theta$ and $\Theta^{-1}$ are continuous; at each $v$, $\Theta(g)_v$ is the image of $g$ under the functoriality of $\mathrm{GL}_2$ applied to the ring homomorphism $\Xi$ followed by evaluation at $v$; $\Theta$ intertwines, for every $K$-algebra automorphism $\sigma$ of $L$, the map induced on $\mathrm{GL}_2$ by $\sigma \otimes \mathrm{id}$ over $\mathbb{A}_{K,\infty}$ with the map induced by $\sigma \otimes \mathrm{id}$ over each $K_v$; and $\Theta$ carries the image of $g \in \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ under $a \mapsto 1 \otimes a$ to the family whose $v$-component is the image of $g_v \in \mathrm{GL}_2(K_v)$ under $a \mapsto 1 \otimes a$.
--
--   This is the archimedean place-by-place decomposition of the group of units of the matrix algebra over $L \otimes_K \mathbb{A}_{K,\infty}$, in the form needed for base change between $K$ and $L$: it transports a decomposition of the underlying ring to $\mathrm{GL}_2$, keeping track both of the Galois twist $\sigma \otimes \mathrm{id}$ and of the embedding of $\mathrm{GL}_2$ over the base. It is used in the archimedean part of the twisted orbital-integral and matching arguments, for instance in the treatment of twisted centralisers and of twisted section functions at regular semisimple elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) :
    ∃ Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)),
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ g v = Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) ∧
      (∀ (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) ∧
      (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (toTensorGL K L (InfiniteAdeleRing K) g) v =
          toTensorGL K L v.Completion
            (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) g)) := by sorry
