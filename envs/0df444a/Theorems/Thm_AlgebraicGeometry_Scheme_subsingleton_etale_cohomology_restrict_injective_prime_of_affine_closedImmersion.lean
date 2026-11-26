-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T04:23:50.121262+00:00
-- url     : https://prove2.me/theorems/1b8a0d7a-a6ef-4122-8682-c4f439cc7a77
-- title:
--   Affine closed-restriction acyclicity for injective prime module sheaves
-- statement:
--   On an affine scheme, the restriction of an injective étale sheaf of $\mathbb Z/\ell\mathbb Z$-modules to a closed subscheme has zero positive-degree cohomology, computed with its underlying abelian sheaf.
-- source:
--   Stacks Project, Lemma 59.82.8, https://stacks.math.columbia.edu/tag/0A51.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion {X Y : Scheme.{u}} [IsAffine X]
    (i : Y ⟶ X) [IsClosedImmersion i] (N : ℕ) (_ : N.Prime)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (_ : Injective J)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (_ : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) : Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves i).obj G).H (q + 1)) := by sorry
