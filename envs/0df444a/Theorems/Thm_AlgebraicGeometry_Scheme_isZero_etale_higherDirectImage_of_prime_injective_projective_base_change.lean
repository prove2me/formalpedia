-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isZero_etale_higherDirectImage_of_prime_injective_projective_base_change
-- name    : AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projective_base_change
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T00:10:38.305424+00:00
-- url     : https://prove2.me/theorems/fbd7a4d6-82e1-40ab-a26a-98c569aaa64b
-- title:
--   Higher base change vanishing for prime-coefficient injectives on projective projections
-- statement:
--   Let $r\colon P\to S$ be the pullback of a projection $\mathbf P^n_R\to\operatorname{Spec}R$. Given an injective sheaf of $\mathbf Z/\ell\mathbf Z$-modules on $P$ for prime $\ell$, pull back its underlying abelian sheaf in any base-change square. Its positive higher direct images along the base-changed projection vanish.
-- source:
--   Stacks Project, Lemmas 59.91.6 and 59.91.10, https://stacks.math.columbia.edu/tag/0A4F.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projective_base_change
    (R : Type u) [CommRing R] (n : ℕ) {P S : Scheme.{u}}
    (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (r : P ⟶ S)
    (h : IsPullback a r (ProjSpace.π R n) v)
    {P' S' : Scheme.{u}} (c : P' ⟶ P) (b : S' ⟶ S) (r' : P' ⟶ S')
    (h' : IsPullback r' c b r)
    (N : ℕ) (hN : N.Prime)
    (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) :
    IsZero (((PhilipponEtaleClosedPushforward.pushforward r').rightDerived (q + 1)).obj ((PhilipponEtaleSmallSite.pullbackSheaves c).obj G)) := by sorry
