-- Prove2me | Theorems.Thm_AlgebraicGeometry_isRegularLocalRing_stalk_of_regular_completed_baseChange
-- name    : AlgebraicGeometry.isRegularLocalRing_stalk_of_regular_completed_baseChange
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-17T21:18:26.844205+00:00
-- url     : https://prove2.me/theorems/150c5426-8eca-4090-857e-c4619e26eadb
-- title:
--   Regularity descends from the actual completed base change
-- statement:
--   Let $f:Y\to X$ be a morphism of locally Noetherian schemes and let $y\in Y$. Put $A=\mathcal O_{X,f(y)}$ and let $\widehat A$ be its maximal-ideal-adic completion. If every local ring of the actual scheme-theoretic pullback
--   $$Y\times_X\operatorname{Spec}(\widehat A)$$
--   is regular, then the original local ring $\mathcal O_{Y,y}$ is regular. The map from the completed local spectrum to $X$ is the canonical one through $\operatorname{Spec}(A)$. There is no finite-type, characteristic, properness or excellence assumption. This supplies the descent step for checking a global modification by its completed local models.
-- source:
--   Stacks Project, Lemma 54.11.1, Tag 0BG5, https://stacks.math.columbia.edu/tag/0BG5 , and the closed-fibre regularity comparison in Lemma 54.11.2(2), Tag 0BG6, https://stacks.math.columbia.edu/tag/0BG6 . This is the consequence obtained by choosing a point above y; local Noetherianity of both original schemes replaces the finite-type assumption used in 54.11.2 to supply Noetherian stalks. The proof constructs that actual point and compares its completed local ring with the original source stalk.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u

theorem AlgebraicGeometry.isRegularLocalRing_stalk_of_regular_completed_baseChange
    {Y X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (y : Y)
    (hreg : let A := X.presheaf.stalk (f y)
      let C := AdicCompletion (maximalIdeal A) A
      let P := pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ X.fromSpecStalk (f y))
      ∀ z : P, IsRegularLocalRing (P.presheaf.stalk z)) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by sorry
