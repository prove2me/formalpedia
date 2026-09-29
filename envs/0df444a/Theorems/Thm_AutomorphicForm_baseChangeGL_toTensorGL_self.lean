-- Prove2me | Theorems.Thm_AutomorphicForm_baseChangeGL_toTensorGL_self
-- name    : AutomorphicForm.baseChangeGL_toTensorGL_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/65079b7e-99e4-5843-9d80-148686bf14bc
-- title:
--   Base change along K/K is the identity on GL₂(A_K)
-- statement:
--   Let $K$ be a number field and let $x$ be an element of $\mathrm{GL}_2(\mathbb{A}_K)$, the general linear group of $2\times 2$ matrices over the adele ring `AdeleRing (𝓞 K) K`. Two maps are involved. First, [`AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K)`](def/AutomorphicForm_TwistedOrbital.html#L71) is the monoid homomorphism $\mathrm{GL}_2(\mathbb{A}_K)\to\mathrm{GL}_2(K\otimes_K\mathbb{A}_K)$ obtained by applying `Matrix.GeneralLinearGroup.map` to the ring homomorphism underlying `Algebra.TensorProduct.includeRight`, i.e. entrywise $a\mapsto 1\otimes a$. Second, [`AutomorphicForm.baseChangeGL K K`](def/AutomorphicForm_BaseChangePlaces.html#L69) is the monoid homomorphism $\mathrm{GL}_2(K\otimes_K\mathbb{A}_K)\to\mathrm{GL}_2(\mathbb{A}_K)$ obtained by applying `Matrix.GeneralLinearGroup.map` to the ring isomorphism [`AutomorphicForm.baseChangeEquiv K K`](def/AutomorphicForm_BaseChangePlaces.html#L65), which is the commutativity isomorphism `Algebra.TensorProduct.comm K K (AdeleRing (𝓞 K) K)` followed by [`M4aHerbrand.Bridge.genuineRingEquiv K K`](def/M4aHerbrand_GenuineTensorEquiv.html#L57). The assertion is that the composite of these two homomorphisms, taken for the trivial extension $L=K$, sends $x$ to $x$; that is, base change along the identity extension is the identity map on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the degeneration of the $\mathrm{GL}_2$ base-change map to the trivial extension $L=K$: it identifies $K\otimes_K\mathbb{A}_K$ with $\mathbb{A}_K$ compatibly with the inclusion $a\mapsto 1\otimes a$, so that the formal base-change machinery is normalised. It is used in the comparison of hyperbolic terms in the winding assembly of the trace-formula argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_baseChangeGL_toTensorGL_self.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.baseChangeGL_toTensorGL_self
    (K : Type) [Field K] [NumberField K] (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.baseChangeGL K K (AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K) x) = x := by sorry
