-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_of_affine_limit
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_of_affine_limit
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T21:51:30.338259+00:00
-- url     : https://prove2.me/theorems/3014a05e-e3ce-49a8-963f-0a5a839a89a7
-- title:
--   Étale cohomology vanishing under a cofiltered limit of affine schemes
-- statement:
--   Let a cofiltered diagram of affine schemes map compatibly to a fixed scheme $X$. If the degree-$q$ cohomology of the pullback of an abelian étale sheaf from $X$ vanishes at every stage, it vanishes on the limit.
-- source:
--   The vanishing consequence of Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_of_affine_limit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_ : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (_ : ∀ i, c.π.app i ≫ g.app i = f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    (∀ i, Subsingleton (((pullbackSheaves (g.app i)).obj F).H q)) →
      Subsingleton (((pullbackSheaves f).obj F).H q) := by sorry
