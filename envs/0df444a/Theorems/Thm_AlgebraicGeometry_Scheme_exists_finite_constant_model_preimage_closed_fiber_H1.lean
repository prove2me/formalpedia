-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_constant_model_preimage_closed_fiber_H1
-- name    : AlgebraicGeometry.Scheme.exists_finite_constant_model_preimage_closed_fiber_H1
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T04:42:41.139696+00:00
-- url     : https://prove2.me/theorems/de7f3262-be69-499f-9e69-c081b5a97f57
-- title:
--   Finite constant models generate degree-one closed-fiber classes
-- statement:
--   Let $J$ be an injective étale sheaf of $\mathbb F_\ell$-modules on a relative projective line over a strictly henselian local ring. For every class in $H^1$ of its restriction to the closed fiber, there is a finite $p\colon Y\to P$ and a morphism $p_*\underline{\mathbb F_\ell}\to J$ from whose restricted $H^1$ the class comes. The map is expressed on the underlying abelian sheaves.
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

theorem AlgebraicGeometry.Scheme.exists_finite_constant_model_preimage_closed_fiber_H1
    (R A : Type u) [CommRing R] [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] (v : Spec (.of A) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of A)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (_ : N.Prime)
    (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (_ : Injective J)
    (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (_ : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (x : ((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj G).H 1) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ P) (_ : IsFinite p)
      (a : ((PhilipponEtaleClosedPushforward.pushforward p).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))) ⟶ G)
      (y : ((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj ((PhilipponEtaleClosedPushforward.pushforward p).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))).H 1),
      (Sheaf.functorH (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r).smallEtaleTopology 1).map
        ((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).map a) y = x := by sorry
