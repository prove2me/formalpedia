-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_projectiveLine_restrict_injective_closed_fiber_one
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_projectiveLine_restrict_injective_closed_fiber_one
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T04:10:10.360327+00:00
-- url     : https://prove2.me/theorems/976fe477-fb01-4a57-91d0-e54269b5ab08
-- title:
--   Degree-one closed-fiber acyclicity of injective prime module sheaves on a projective line
-- statement:
--   On a relative projective line over a strictly henselian local ring, let $J$ be an injective étale sheaf of $\mathbb Z/\ell\mathbb Z$-modules for a prime $\ell$. The restriction of its underlying abelian sheaf to the closed fiber has zero $H^1$.
-- source:
--   Stacks Project, Lemma 59.85.2, https://stacks.math.columbia.edu/tag/0A5H.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_projectiveLine_restrict_injective_closed_fiber_one
    (R A : Type u) [CommRing R] [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] (v : Spec (.of A) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of A)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (_ : N.Prime)
    (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (_ : Injective J)
    (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (_ : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u}) :
    Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj G).H 1) := by sorry
