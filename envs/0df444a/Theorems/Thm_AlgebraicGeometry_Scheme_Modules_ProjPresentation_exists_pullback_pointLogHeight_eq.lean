-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_pullback_pointLogHeight_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_pullback_pointLogHeight_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:26.35966+00:00
-- url     : https://prove2.me/theorems/6854102c-fbb7-47ea-a43e-4c188dfb4170
-- title:
--   Pulling back a projective presentation pulls back its sections, map, and height
-- statement:
--   Let $p:Y→X$ be a morphism over a number field and let $P$ be a projective presentation of a module $M$ on $X$. There exists a presentation $P'$ of $p^*M$ whose sections are the pulled-back sections of $P$, whose projective map is $p$ followed by the map of $P$, and for every $K$-point $y$, $$h_{P'}(y)=h_P(p(y)).$$ This gives functoriality of the presentation height.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_pullback_pointLogHeight_eq
    {K : Type} [Field K] [NumberField K]
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    (p : Y ⟶ X) {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) :
    ∃ P' : ((Scheme.Modules.pullback p).obj M).ProjPresentation (p ≫ f) N,
      (∀ i, P'.σ i =
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤)
          (P.σ i)) ∧
      P'.toProj = p ≫ P.toProj ∧
      ∀ y : Scheme.KPoint (p ≫ f),
        P'.pointLogHeight y =
          P.pointLogHeight
            ⟨y.1 ≫ p, by rw [Category.assoc, y.2]⟩ := by sorry
