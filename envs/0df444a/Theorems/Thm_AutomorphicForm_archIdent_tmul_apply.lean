-- Prove2me | Theorems.Thm_AutomorphicForm_archIdent_tmul_apply
-- name    : AutomorphicForm.archIdent_tmul_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/fcbab550-c937-5476-bd98-6e33e215e968
-- title:
--   Value of the archimedean base-change map on a pure tensor
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $x \in L$, let $a$ be an element of the infinite adele ring $\mathbb{A}_{K,\infty} = \prod_{v \mid \infty} K_v$ of $K$, and let $w$ be an infinite place of $L$; write $v = w.\mathrm{comap}\,(\mathrm{algebraMap}\;K\;L)$ for the place of $K$ below $w$, and equip the associated valuation subring data with the instance recording that $w$ lies over $v$ (by definitional equality). The map `archIdent K L` is the ring homomorphism $L \otimes_K \mathbb{A}_{K,\infty} \to \mathbb{A}_{L,\infty}$ obtained by first applying the commutation isomorphism $L \otimes_K \mathbb{A}_{K,\infty} \cong \mathbb{A}_{K,\infty} \otimes_K L$ and then the ring equivalence `baseChangeRingEquiv` attached to the infinite-place data `genuineInfinitePlaceData`, i.e. the decomposition $\mathbb{A}_{K,\infty} \otimes_K L \cong \prod_v (K_v \otimes_K L)$ followed by the per-place isomorphisms supplied by `placeEquivAlg` and the collapsing of the places of $L$ above each $v$. The assertion is that the $w$-component of $\mathrm{archIdent}(x \otimes_K a)$ equals the product, inside the completion $L_w$, of the image of the $v$-component $a_v \in K_v$ under the structure map $K_v \to L_w$ with the image of $x$ under $L \to L_w$.
--
--   This is the explicit formula for the canonical isomorphism $L \otimes_K \mathbb{A}_{K,\infty} \cong \mathbb{A}_{L,\infty}$ evaluated on pure tensors, read off one archimedean place at a time. It is the computational interface through which archimedean test data written as elements of $L \otimes_K \mathbb{A}_{K,\infty}$ are converted into per-place coordinates; it is used in the analysis of archimedean evaluation maps and of matching conditions for automorphic forms, for instance in [`AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj`](thm.html#AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj) and [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archIdent_tmul_apply.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

theorem AutomorphicForm.archIdent_tmul_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace L) :
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    archIdent K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by sorry
