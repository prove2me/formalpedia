-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_surjective_etale_H1_unit_constant_closed_fiber_of_isProper
-- name    : AlgebraicGeometry.Scheme.surjective_etale_H1_unit_constant_closed_fiber_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T04:42:37.455871+00:00
-- url     : https://prove2.me/theorems/4d16af58-ab67-40c7-a5c6-37b28e21603d
-- title:
--   Degree-one constant étale classes lift from a proper closed fiber
-- statement:
--   For a proper scheme over a strictly henselian local ring and a prime $\ell$, the restriction unit induces a surjection from $H^1$ of the constant cyclic sheaf to $H^1$ of the direct image of its inverse image on the closed fiber. Exactness of direct image for the closed immersion identifies the target with the corresponding group on the closed fiber.
-- source:
--   Stacks Project, Lemma 59.85.1, https://stacks.math.columbia.edu/tag/0A5G.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.surjective_etale_H1_unit_constant_closed_fiber_of_isProper
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (_ : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (N : ℕ) (_ : N.Prime) :
    Function.Surjective ((Sheaf.functorH Y.smallEtaleTopology 1).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction j).unit.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) := by sorry
