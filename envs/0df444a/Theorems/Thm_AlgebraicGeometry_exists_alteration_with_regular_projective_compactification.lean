-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_alteration_with_regular_projective_compactification
-- name    : AlgebraicGeometry.exists_alteration_with_regular_projective_compactification
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-28T18:15:35.874038+00:00
-- url     : https://prove2.me/theorems/573720b0-e7d9-43fd-b77a-beafb8ac75bc
-- title:
--   Alterations with regular projective compactification
-- statement:
--   Let $K$ be an arbitrary field and let $X$ be an integral separated $K$-scheme of finite type. There are an integral scheme $Z$ and a proper dominant $K$-morphism
--   $$a:Z\longrightarrow X$$
--   which is finite over a nonempty open subscheme of $X$.
--
--   The alteration source $Z$ admits a dense open immersion into an integral regular projective $K$-scheme $Y$. More precisely, there are compatible $K$-morphisms
--   $$c:Z\hookrightarrow Y,\qquad j:Y\hookrightarrow\mathbb P^m_K,$$
--   where $j$ is a closed immersion and every local ring of $Y$ is regular.
--
--   The target $X$ need not be proper or normal. No perfectness, algebraic closedness or dimension hypothesis is imposed on $K$ or $X$. Regularity over an imperfect field does not assert smoothness. The normal-crossings boundary conclusion of the source theorem is omitted.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1, p. 66, and the definition of alteration in Section 2.20, p. 61; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Take the specified proper closed subset to be empty, retain the proper dominant generically finite alteration and its regular projective compactification, and omit the normal-crossings divisor assertion. Finite type is expressed by LocallyOfFiniteType and QuasiCompact; the same structure morphisms are used in all compatibility equalities. This remains an Open external theorem, including its stable-curve and regularization construction; no ancestor theorem is imported.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_alteration_with_regular_projective_compactification
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by sorry
