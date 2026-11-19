-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_proper_compactification_sup_of_isAffineOpen
-- name    : AlgebraicGeometry.exists_proper_compactification_sup_of_isAffineOpen
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-18T14:29:12.458217+00:00
-- url     : https://prove2.me/theorems/5b55ab9a-bafd-4d2d-8b28-7d6d8218b997
-- title:
--   Attach one affine open in a Nagata compactification
-- statement:
--   Let $X$ be an integral separated scheme of finite type over a field $K$. Let $U,V\subseteq X$ be nonempty opens with $V$ affine. Suppose $U$ has a compactification over $K$, given by an open immersion $U\hookrightarrow C$ into a proper $K$-scheme. Then the open subscheme $U\cup V$ has a compactification over $K$ as well. The open immersion into the new proper scheme must recover the original structure morphism of $U\cup V$ upon composition with its map to $\operatorname{Spec}K$. The new proper scheme need not map to the supplied compactification of $U$.
-- source:
--   Stacks Project, Lemma 38.33.7, Tag 0F40, https://stacks.math.columbia.edu/tag/0F40 . This is the case with base Spec K and one affine open. Its compactification is available by projective closure, and the intersection is dense because the two opens are nonempty in an integral scheme.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.exists_proper_compactification_sup_of_isAffineOpen
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    (U V : X.Opens) (hU : Nonempty U) (hV : Nonempty V) (hAff : IsAffineOpen V)
    (C : Scheme.{u}) (q : C ⟶ Spec (.of K)) [IsProper q]
    (j : U.toScheme ⟶ C) [IsOpenImmersion j] (hj : j ≫ q = U.ι ≫ π) :
    ∃ (D : Scheme.{u}) (p : D ⟶ Spec (.of K)) (i : (U ⊔ V).toScheme ⟶ D),
      IsProper p ∧ IsOpenImmersion i ∧ i ≫ p = (U ⊔ V).ι ≫ π := by sorry
