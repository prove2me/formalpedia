-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_representation_constant_torsor_of_ne_zero
-- name    : AlgebraicGeometry.Scheme.exists_finite_etale_representation_constant_torsor_of_ne_zero
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T07:08:38.272183+00:00
-- url     : https://prove2.me/theorems/f73fd62c-3da8-4bd6-ad15-973402e083ec
-- title:
--   Finite étale representability of a finite constant torsor
-- statement:
--   For a nonzero modulus N, a torsor under the pullback of the constant ZMod N étale sheaf is represented on the small étale site by a finite étale scheme.
-- source:
--   Stacks Project, Lemma 59.64.4, https://stacks.math.columbia.edu/tag/03RV.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_etale_representation_constant_torsor_of_ne_zero
    {Y T : Scheme.{u}} (j : T ⟶ Y) (N : ℕ) (_ : N ≠ 0)
    (B : PhilipponTorsorSectionFibers.Torsor ((PhilipponEtaleSmallSite.pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) :
    ∃ V : T.Etale, IsFinite V.hom ∧ Nonempty (yoneda.obj V ≅ B.D.P) := by sorry
