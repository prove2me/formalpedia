-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_two_chart_blowup_model_of_isAffineOpen
-- name    : AlgebraicGeometry.exists_two_chart_blowup_model_of_isAffineOpen
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-18T15:39:24.615951+00:00
-- url     : https://prove2.me/theorems/c7161021-4529-43b7-9103-555ac01697a0
-- title:
--   Prepare two blowup charts for affine attachment
-- statement:
--   Let X be integral, separated and finite type over a field K, with nonempty opens U and V, V affine, and a given proper compactification of U. Put T = U ∪ V. There exists a separated finite-type K-scheme W with an open immersion i of T over K. There also exists a proper integral K-scheme G covered by two opens D and E, with K-morphisms from D to A and from E to B. Give ideal sheaves on A and B and blowup morphisms pL: L → A and pR: R → B, expressed by their unique lifting property for morphisms pulling the centers back to invertible ideals. The chart maps L → W and R → W are over K. A nonempty scheme O has an open immersion s into G factoring through D and E, and a map v into T for which i ∘ v is dominant. Along the two maps O → D → A and O → E → B the centers pull back to the unit ideal. There are compatible lifts O → L and O → R over the respective chart bases, both giving i ∘ v upon composition into W.
-- source:
--   Geometric preparation in Stacks Project, Lemma 38.33.7 (https://stacks.math.columbia.edu/tag/0F40), through the separated amalgam construction, before the properness argument. Use Lemma 38.33.6 (https://stacks.math.columbia.edu/tag/0F3Z) for the proper extensions, Lemma 38.33.4 (https://stacks.math.columbia.edu/tag/0F3X) for the separated amalgam and Lemma 31.35.2 (https://stacks.math.columbia.edu/tag/080L) for composition of the admissible blowups.

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_two_chart_blowup_model_of_isAffineOpen
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    (U V : X.Opens) (hU : Nonempty U) (hV : Nonempty V) (hAff : IsAffineOpen V)
    (C : Scheme.{u}) (qC : C ⟶ Spec (.of K)) [IsProper qC]
    (j : U.toScheme ⟶ C) [IsOpenImmersion j] (hj : j ≫ qC = U.ι ≫ π) :
    ∃ (W G O A B L R : Scheme.{u})
      (q : W ⟶ Spec (.of K)) (g : G ⟶ Spec (.of K))
      (i : (U ⊔ V).toScheme ⟶ W) (v : O ⟶ (U ⊔ V).toScheme) (s : O ⟶ G)
      (D E : G.Opens) (sD : O ⟶ D.toScheme) (sE : O ⟶ E.toScheme)
      (a : D.toScheme ⟶ A) (b : E.toScheme ⟶ B)
      (qA : A ⟶ Spec (.of K)) (qB : B ⟶ Spec (.of K))
      (I : A.IdealSheafData) (J : B.IdealSheafData)
      (pL : L ⟶ A) (pR : R ⟶ B) (iL : L ⟶ W) (iR : R ⟶ W)
      (sL : O ⟶ L) (sR : O ⟶ R),
      IsOpenImmersion i ∧ i ≫ q = (U ⊔ V).ι ≫ π ∧
      IsSeparated q ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
      IsIntegral G ∧ IsProper g ∧ Nonempty O ∧ IsOpenImmersion s ∧ IsDominant (v ≫ i) ∧
      D ⊔ E = ⊤ ∧ sD ≫ D.ι = s ∧ sE ≫ E.ι = s ∧
      a ≫ qA = D.ι ≫ g ∧ b ≫ qB = E.ι ≫ g ∧
      I.comap (sD ≫ a) = ⊤ ∧ J.comap (sE ≫ b) = ⊤ ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ A), (I.comap f).IsInvertible → ∃! l : Y ⟶ L, l ≫ pL = f) ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ B), (J.comap f).IsInvertible → ∃! r : Y ⟶ R, r ≫ pR = f) ∧
      iL ≫ q = pL ≫ qA ∧ iR ≫ q = pR ≫ qB ∧
      sL ≫ pL = sD ≫ a ∧ sR ≫ pR = sE ≫ b ∧ sL ≫ iL = v ≫ i ∧ sR ≫ iR = v ≫ i := by sorry
