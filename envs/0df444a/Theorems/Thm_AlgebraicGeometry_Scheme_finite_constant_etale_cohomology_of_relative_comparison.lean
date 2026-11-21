-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_relative_comparison
-- name    : AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_relative_comparison
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T19:49:16.014633+00:00
-- url     : https://prove2.me/theorems/3d38c2f0-1616-41bb-998f-bea0f81e0bdf
-- title:
--   Finiteness from relative étale cohomology comparison
-- statement:
--   Let $f\colon Y\to X$ be a scheme morphism, let $Z\hookrightarrow X$ be a closed immersion, and let $E=Y\times_X Z$. Fix an abelian coefficient group $A$. Assume that the relative constant cohomology groups of $(X,Z)$ and $(Y,E)$ are isomorphic in every degree, and that constant étale cohomology of $Y$, $Z$, and $E$ is finite in every degree. Then the constant étale cohomology of $X$ is finite in every degree. This is the finiteness consequence of the two exact restriction sequences.
-- source:
--   Stacks Project, Lemma 59.70.8 (https://stacks.math.columbia.edu/tag/095L) and the long exact cohomology sequence (https://stacks.math.columbia.edu/tag/03Q3).

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_relative_comparison
    (A : Type u) [AddCommGroup A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (hrel : ∀ q, Nonempty ((PhilipponEtaleRelativeCohomology.relativeConstant i A).H q ≃+
      (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A).H q))
    (hY : ∀ q, Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (hZ : ∀ q, Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q))
    (hE : ∀ q, Finite (((constantSheaf (pullback f i).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by sorry
