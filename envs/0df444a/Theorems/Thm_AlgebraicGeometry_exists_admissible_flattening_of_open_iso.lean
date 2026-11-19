-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_admissible_flattening_of_open_iso
-- name    : AlgebraicGeometry.exists_admissible_flattening_of_open_iso
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-18T16:37:41.663975+00:00
-- url     : https://prove2.me/theorems/aa0c29cf-76d9-4fd9-a88e-f41b43efc8bc
-- title:
--   Admissible flattening over a protected open isomorphism
-- statement:
--   Let $f\colon X\to Y$ be a separated morphism of finite type between integral Noetherian schemes. Let $U$ be a nonempty scheme admitting open immersions $s\colon U\hookrightarrow X$ and $j\colon U\hookrightarrow Y$ with $f\circ s=j$. There is an ideal sheaf $I$ on $Y$ which restricts to the unit ideal on $U$ and yields a flat strict transform. In detail, for the blowups $p\colon X'\to X$ in $I\mathcal O_X$ and $q\colon Y'\to Y$ in $I$, the induced morphism $$X'\longrightarrow Y'$$ is flat. Both blowups in the formal statement are specified by invertibility of their pulled-back ideals and their unique lifting properties.
-- source:
--   Stacks Project Lemma 38.31.1 (https://stacks.math.columbia.edu/tag/081R) applied over the given open isomorphism, with the identification of the strict transform in Lemma 31.34.2 (https://stacks.math.columbia.edu/tag/080E).

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.exists_admissible_flattening_of_open_iso
    {X Y U : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] [Nonempty U]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (s : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion j]
    (hs : s ≫ f = j) :
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
