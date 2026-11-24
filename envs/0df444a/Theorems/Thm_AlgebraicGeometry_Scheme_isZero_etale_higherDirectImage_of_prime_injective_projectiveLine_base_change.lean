-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change
-- name    : AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T02:14:30.08384+00:00
-- url     : https://prove2.me/theorems/34f18e69-ec82-4818-a272-82fbaba422a3
-- title:
--   Higher base-change vanishing for prime-coefficient injectives on the projective line
-- statement:
--   Let $r\colon\mathbf P^1_S\to S$ be the projection, presented by a pullback from a projective line over an affine base. Pull back the underlying abelian étale sheaf of any injective $\mathbf Z/\ell\mathbf Z$-module sheaf along a base change of $r$, where $\ell$ is prime. The positive higher direct images of the pulled-back sheaf along the changed projection vanish.
-- source:
--   Stacks Project, Theorem 59.91.11, https://stacks.math.columbia.edu/tag/095T.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change
    (R : Type u) [CommRing R] {S : Scheme.{u}} (v : S ⟶ Spec (.of R))
    {P' S' : Scheme.{u}} (c : P' ⟶ pullback v (ProjSpace.π R 1)) (b : S' ⟶ S) (r' : P' ⟶ S')
    (h : IsPullback r' c b (pullback.fst v (ProjSpace.π R 1)))
    (N : ℕ) (hN : N.Prime)
    (J : Sheaf (pullback v (ProjSpace.π R 1)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf (pullback v (ProjSpace.π R 1)).smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) :
    IsZero (((PhilipponEtaleClosedPushforward.pushforward r').rightDerived (q + 1)).obj ((PhilipponEtaleSmallSite.pullbackSheaves c).obj G)) := by sorry
