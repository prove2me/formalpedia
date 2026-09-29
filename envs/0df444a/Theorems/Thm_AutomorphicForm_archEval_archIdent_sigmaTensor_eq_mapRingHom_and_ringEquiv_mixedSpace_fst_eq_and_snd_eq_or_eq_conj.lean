-- Prove2me | Theorems.Thm_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
-- name    : AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/640dd442-6842-5e38-b480-68d70490f155
-- title:
--   Transport of places under g⊗ 1 on L⊗_K K_∞
-- statement:
--   Let $K\subseteq L$ be number fields, let $g$ be a $K$-algebra automorphism of $L$, and let $w'$ be an infinite place of $L$; write $w'\circ g$ for `w'.comap (g : L →+* L)`. Here [`AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g`](def/AutomorphicForm_TwistedOrbital.html#L199) is the ring endomorphism $g\otimes\mathrm{id}$ of $L\otimes_K \mathbb{A}_{K,\infty}$, [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420) is the ring homomorphism $L\otimes_K\mathbb{A}_{K,\infty}\to\mathbb{A}_{L,\infty}$ obtained by commuting the two factors and then applying the base-change isomorphism $\mathbb{A}_{K,\infty}\otimes_K L\cong\mathbb{A}_{L,\infty}$ attached to the infinite-place data `genuineInfinitePlaceData`, and `archEval L w` is evaluation at $w$, i.e. the $w$-component of an element of $\mathbb{A}_{L,\infty}$. The conclusion is a fivefold conjunction. First, the map $L\to L$ given by $g$, read from the absolute-value structure of $w'\circ g$ to that of $w'$, is an isometry. Second, for any proof $h$ of that isometry and all $y\in L\otimes_K\mathbb{A}_{K,\infty}$, the $w'$-component of $\mathrm{archIdent}((g\otimes1)y)$ is the image of the $(w'\circ g)$-component of $\mathrm{archIdent}(y)$ under the ring homomorphism of completions induced by $h$. Third, the corresponding norms agree. Fourth, if $w'$ and an infinite place $w''$ are both real and $w''=w'\circ g$, then for all $y$ the real coordinate at $w'$ of $\mathrm{archIdent}((g\otimes1)y)$ in the mixed space of $L$ equals the real coordinate at $w''$ of $\mathrm{archIdent}(y)$. Fifth, if $w'$ and $w''$ are both complex with $w''=w'\circ g$, then either the complex coordinate at $w'$ of $\mathrm{archIdent}((g\otimes1)y)$ equals that at $w''$ of $\mathrm{archIdent}(y)$ for all $y$, or it equals its complex conjugate for all $y$.
--
--   This is the Galois equivariance (place transport) of the archimedean base-change identification $L\otimes_K\mathbb{A}_{K,\infty}\cong\mathbb{A}_{L,\infty}$: twisting by $g\otimes 1$ moves the $w'$-component to the $(w'\circ g)$-component, isometrically, and in mixed-space coordinates acts by the identity on real places and by the identity or complex conjugation on complex places. It is used in the computations of norms of archimedean evaluations of resolvents at real and complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : L ≃ₐ[K] L) (w' : NumberField.InfinitePlace L) :
    Isometry (((WithAbs.equiv w'.1).symm.toRingHom.comp
          ((g : L ≃ₐ[K] L).toRingEquiv.toRingHom.comp (WithAbs.equiv (w'.comap (g : L →+* L)).1).toRingHom)) :
        WithAbs (w'.comap (g : L →+* L)).1 → WithAbs w'.1) ∧
    (∀ h : Isometry (((WithAbs.equiv w'.1).symm.toRingHom.comp
          ((g : L ≃ₐ[K] L).toRingEquiv.toRingHom.comp (WithAbs.equiv (w'.comap (g : L →+* L)).1).toRingHom)) :
        WithAbs (w'.comap (g : L →+* L)).1 → WithAbs w'.1),
      ∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).toCompletion =
          h.mapRingHom (NumberField.AdelicLevel.archEval L (w'.comap (g : L →+* L)) (AutomorphicForm.archIdent K L y)).toCompletion) ∧
    (∀ y : (L ⊗[K] InfiniteAdeleRing K),
      ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))‖ =
        ‖NumberField.AdelicLevel.archEval L (w'.comap (g : L →+* L)) (AutomorphicForm.archIdent K L y)‖) ∧
    (∀ (w'' : NumberField.InfinitePlace L) (hw' : w'.IsReal) (hw'' : w''.IsReal),
      w'' = w'.comap (g : L →+* L) →
      ∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).1 ⟨w', hw'⟩ =
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).1 ⟨w'', hw''⟩) ∧
    (∀ (w'' : NumberField.InfinitePlace L) (hw' : w'.IsComplex) (hw'' : w''.IsComplex),
      w'' = w'.comap (g : L →+* L) →
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).2 ⟨w', hw'⟩ =
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w'', hw''⟩) ∨
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).2 ⟨w', hw'⟩ =
          (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w'', hw''⟩))) := by sorry
