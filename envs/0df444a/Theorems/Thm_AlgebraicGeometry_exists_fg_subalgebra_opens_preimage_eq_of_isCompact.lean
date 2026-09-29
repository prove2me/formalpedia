-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact
-- name    : AlgebraicGeometry.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/6baf3783-672e-5557-8226-f74e54809cdb
-- title:
--   Quasi-compact opens descend to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra (both in a fixed universe), let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} A_0$ be a morphism that is quasi-compact and quasi-separated. Write $X_A$ for the pullback of $f$ along $\operatorname{Spec}$ of the structure map $A_0 \to A$. Given an open subset $W$ of $X_A$ whose underlying set is compact, and a finite subset $s$ of $A$, the assertion is that there exists an $A_0$-subalgebra $T \subseteq A$ which is finitely generated as an $A_0$-algebra and contains $s$, together with an open subset $W_0$ of the pullback $X_T$ of $f$ along $\operatorname{Spec}(A_0 \to T)$ whose underlying set is compact, such that: for every morphism $q \colon X_A \to X_T$ satisfying $q$ followed by the first projection of $X_T$ equals the first projection of $X_A$, and $q$ followed by the second projection of $X_T$ equals the second projection of $X_A$ followed by $\operatorname{Spec}$ of the inclusion $T \hookrightarrow A$, one has $q^{-1}(W_0) = W$ as opens of $X_A$. The comparison morphism is thus not constructed in the statement but characterised by its two projection equations.
--
--   This is the descent of a quasi-compact open subset of a base change along a directed union of finitely generated subalgebras, in the style of EGA IV₃ 8.3: $X_A$ is the limit of the schemes $X_T$ over the finitely generated $A_0$-subalgebras $T$ of $A$ containing a prescribed finite set. It feeds the gluing step of [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation), where an open cover of a base change must be realised over a single finitely generated stage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).Opens)
    (hW : IsCompact (W : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ W₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Opens,
        IsCompact (W₀ : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) ∧
        ∀ q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          q ≫ pullback.fst f _ = pullback.fst f _ →
          q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q ⁻¹ᵁ W₀ = W := by sorry
