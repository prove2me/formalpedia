-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_surjective_etale_H1_unit_finiteConstant_closed_fiber
-- name    : AlgebraicGeometry.Scheme.surjective_etale_H1_unit_finiteConstant_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T05:14:05.100572+00:00
-- url     : https://prove2.me/theorems/0f7c2df7-6b85-45e7-8448-c03730b42ffd
-- title:
--   Degree-one classes lift for finite direct images of constant cyclic sheaves
-- statement:
--   Let $P$ be proper over a strictly henselian local ring and $p\colon Y\to P$ finite. For a prime $\ell$, the restriction unit on the finite direct image $p_*\underline{\mathbb F_\ell}$ induces a surjection in degree-one étale cohomology. The closed-fiber group is expressed using the direct image of the restricted sheaf.
-- source:
--   Stacks Project, Proof of Lemma 59.85.2, https://stacks.math.columbia.edu/tag/0A5H.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.surjective_etale_H1_unit_finiteConstant_closed_fiber
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {P Y : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [IsProper r]
    (p : Y ⟶ P) [IsFinite p] (N : ℕ) (_ : N.Prime) :
    Function.Surjective ((Sheaf.functorH P.smallEtaleTopology 1).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).unit.app ((PhilipponEtaleClosedPushforward.pushforward p).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))))) := by sorry
