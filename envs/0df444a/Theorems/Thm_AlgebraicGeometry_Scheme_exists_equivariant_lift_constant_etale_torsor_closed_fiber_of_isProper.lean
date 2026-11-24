-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper
-- name    : AlgebraicGeometry.Scheme.exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T05:59:08.169423+00:00
-- url     : https://prove2.me/theorems/deab9805-6bd4-4e97-b9ca-4a0967aaa784
-- title:
--   Finite constant étale torsors lift equivariantly from a proper closed fiber
-- statement:
--   Let $Y$ be proper over a strictly henselian local ring and let $j:T\to Y$ be its closed fiber. A torsor on $T$ under the restriction of the constant cyclic sheaf of prime order lifts to a torsor on $Y$ together with a map on sections over each base-changed étale chart compatible with restriction of the coefficient sheaf.
-- source:
--   Stacks Project, Lemmas 58.9.1 and 59.64.4, https://stacks.math.columbia.edu/tag/0A48.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem AlgebraicGeometry.Scheme.exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (_ : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (N : ℕ) (_ : N.Prime)
    (B : PhilipponTorsorSectionFibers.Torsor ((PhilipponEtaleSmallSite.pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) :
    ∃ (D : PhilipponTorsorSectionFibers.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))) (d : D.D.P ⟶ (PhilipponEtaleBaseChangeComparison.baseChange j).op ⋙ B.D.P),
      ∀ (U : Y.Etaleᵒᵖ) (x y : D.D.P.obj U),
        B.D.diff ((PhilipponEtaleBaseChangeComparison.baseChange j).op.obj U) (d.app U x) (d.app U y) =
          ((PhilipponEtaleSmallSite.pullbackAdjunction j).unit.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))).hom.app U (D.D.diff U x y) := by sorry
