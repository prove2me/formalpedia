-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_closed_fiber
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T03:28:33.44361+00:00
-- url     : https://prove2.me/theorems/ac2bbc25-55a6-4c8f-ba05-b80397459682
-- title:
--   Higher étale cohomology of a strictly henselian projective line and its closed fiber
-- statement:
--   Let $P$ be a relative projective line over a strictly henselian local ring. The positive-degree étale cohomology of every abelian sheaf on $P$ annihilated by a prime $ℓ$ agrees with that of its inverse image on the closed fiber.
-- source:
--   Stacks Project, Lemma 59.85.2 and Theorem 59.91.11, https://stacks.math.columbia.edu/tag/0A5H.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_closed_fiber
    (R A : Type u) [CommRing R] [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] (v : Spec (.of A) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of A)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (_ : N.Prime) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (_ : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj F).H (q + 1))) := by sorry
