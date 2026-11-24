-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_directImage_baseChange_of_projective_projection
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_directImage_baseChange_of_projective_projection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-23T23:49:19.864909+00:00
-- url     : https://prove2.me/theorems/8fbabbbb-bb32-491a-882c-97c4c0bdc85a
-- title:
--   Ordinary étale direct image for projective projections commutes with base change
-- statement:
--   Let $r\colon P\to S$ be the pullback of a projection $\mathbf P^n_R\to\operatorname{Spec}R$. For every pullback square along $r$ and every abelian étale sheaf $F$ on $P$, the inverse image of $r_*F$ is isomorphic to the direct image of the inverse image of $F$.
-- source:
--   Stacks Project, Lemma 59.91.5, https://stacks.math.columbia.edu/tag/0A3U.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.nonempty_etale_directImage_baseChange_of_projective_projection
    (R : Type u) [CommRing R] (n : ℕ) {P S : Scheme.{u}}
    (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (r : P ⟶ S)
    (h : IsPullback a r (ProjSpace.π R n) v)
    {P' S' : Scheme.{u}} (c : P' ⟶ P) (b : S' ⟶ S) (r' : P' ⟶ S')
    (h' : IsPullback r' c b r)
    (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) :
    Nonempty ((PhilipponEtaleSmallSite.pullbackSheaves b).obj ((PhilipponEtaleClosedPushforward.pushforward r).obj F) ≅
      (PhilipponEtaleClosedPushforward.pushforward r').obj ((PhilipponEtaleSmallSite.pullbackSheaves c).obj F)) := by sorry
