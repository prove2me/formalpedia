-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/8525db44-85ad-5422-950c-16c8367ec9ad
-- title:
--   Equality of morphisms descends to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra, let $X_1,X_2$ be schemes, and let $f_1\colon X_1\to\operatorname{Spec}A_0$ and $f_2\colon X_2\to\operatorname{Spec}A_0$ be morphisms with $f_1$ quasi-compact and $f_2$ locally of finite type. Let $a,b\colon X_1\to X_2$ be two morphisms over $\operatorname{Spec}A_0$, that is, $a$ followed by $f_2$ and $b$ followed by $f_2$ both equal $f_1$. Assume that $a$ and $b$ agree after base change to $A$: writing $\mathrm{pr}_1$ for the first projection of the pullback of $f_1$ along $\operatorname{Spec}$ of the structure map $A_0\to A$, the composites $\mathrm{pr}_1$ followed by $a$ and $\mathrm{pr}_1$ followed by $b$ coincide. Then for every finite subset $s\subseteq A$ there exists an $A_0$-subalgebra $T\subseteq A$ which is finitely generated as an $A_0$-algebra and contains $s$, such that $a$ and $b$ already agree after base change to $T$: the first projection of the pullback of $f_1$ along $\operatorname{Spec}$ of $A_0\to T$, composed with $a$, equals the same projection composed with $b$.
--
--   This is the injectivity half of the statement that $\operatorname{Hom}_{\operatorname{Spec}A_0}(\varprojlim_T X_1\times_{\operatorname{Spec}A_0}\operatorname{Spec}T,\,X_2)=\varinjlim_T\operatorname{Hom}_{\operatorname{Spec}A_0}(X_1\times_{\operatorname{Spec}A_0}\operatorname{Spec}T,\,X_2)$ for $X_2$ locally of finite type over $\operatorname{Spec}A_0$, specialised to the directed system of finitely generated $A_0$-subalgebras of $A$. It belongs to the Noetherian-approximation toolkit of the formalisation, and is used for the version quantified over families of pairs of morphisms, for descending isomorphisms of pullbacks along morphisms locally of finite presentation, and in the Čerednik–Drinfel'd constructions with fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [LocallyOfFiniteType f₂]
    (a b : X₁ ⟶ X₂) (ha : a ≫ f₂ = f₁) (hb : b ≫ f₂ = f₁)
    (hab : pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ a =
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ b) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ a =
        pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ b := by sorry
