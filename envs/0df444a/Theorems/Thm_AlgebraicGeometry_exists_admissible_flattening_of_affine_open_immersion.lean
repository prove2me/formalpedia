-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_admissible_flattening_of_affine_open_immersion
-- name    : AlgebraicGeometry.exists_admissible_flattening_of_affine_open_immersion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-18T17:10:53.436244+00:00
-- url     : https://prove2.me/theorems/d5f14bab-24e3-4fb2-ac11-e7895fc92e4b
-- title:
--   Admissible flattening for affine schemes and a protected open
-- statement:
--   Let $f\colon X\to Y$ be a dominant finite-type morphism of integral Noetherian affine schemes. Let $U$ be a nonempty open subscheme of $Y$ over which $X\times_Y U\to U$ is an open immersion. There is an ideal sheaf $I$ on $Y$ restricting to the unit ideal on $U$. After blowing up $I$ on $Y$ and its pullback on $X$, the induced morphism $$X^{\prime}\longrightarrow Y^{\prime}$$ is flat. The statement gives the blowups by their universal lifting properties and the invertibility of the pulled-back ideals.
-- source:
--   Affine case of Stacks Project Lemma 38.31.1 (https://stacks.math.columbia.edu/tag/081R). Identify the strict transform with the blowup of the pulled-back ideal using Lemma 31.34.2 (https://stacks.math.columbia.edu/tag/080E). An open immersion over the protected open is flat and locally of finite presentation.

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.exists_admissible_flattening_of_affine_open_immersion
    {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [IsAffine X] [IsAffine Y] [Nonempty U]
    (f : X ⟶ Y) [IsDominant f] [IsSeparated f] [LocallyOfFiniteType f]
    (j : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion (f ∣_ j.opensRange)] :
    ∃ I : Y.IdealSheafData, I.comap j = ⊤ ∧
      ∀ (X' Y' : Scheme.{u}) (p : X' ⟶ X) (q : Y' ⟶ Y) (m : X' ⟶ Y'),
        m ≫ q = p ≫ f →
        ((I.comap f).comap p).IsInvertible →
        (I.comap q).IsInvertible →
        (∀ (Z : Scheme.{u}) (g : Z ⟶ X), ((I.comap f).comap g).IsInvertible →
          ∃! l : Z ⟶ X', l ≫ p = g) →
        (∀ (Z : Scheme.{u}) (g : Z ⟶ Y), (I.comap g).IsInvertible →
          ∃! l : Z ⟶ Y', l ≫ q = g) →
        Flat m := by sorry
