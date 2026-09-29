-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isFinite_proj_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
-- name    : AlgebraicGeometry.RelPicard.exists_isFinite_proj_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/302fe347-2367-54fe-81ed-863397981447
-- title:
--   Relative Pic⁰ is finite over a Proj
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c\colon C\to\operatorname{Spec} R$ be a proper morphism of schemes that is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R\to C$ composing with $c$ to the identity. Assume the hypothesis `h𝔉`: for every $m_0\in\mathbb N$ there is a `FiniteMapData` for $(c,\varepsilon)$ with invariant $m\ge m_0$, that is, affine opens $U,V$ of $C$ with $U\sqcup$-union $V=\top$, $U$ exactly the complement of the image of $\varepsilon$, sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ whose restrictions to $U\cap V$ are mutually inverse, with $U\cap V$ equal to the basic open of $f$ and to that of $g$, such that $R[X]\to\Gamma(C,U)$, $X\mapsto f$, and $R[X]\to\Gamma(C,V)$, $X\mapsto g$, are finite, and such that for every local $R$-algebra $S$ and every $s\in S$ the quotient $S\otimes_R\Gamma(C,U)/(1\otimes f-s\otimes 1)$ is finite free of rank $m$ over $S$. Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the algebraic-equivalence-to-zero cut of the rigidified relative Picard functor: $h$ provides a rigidified line bundle (the Poincaré bundle) on $C\times_{\operatorname{Spec} R}D.P$ which is fibrewise algebraically equivalent to zero over every algebraically closed point of $D.P$, such that for every $t\colon T\to\operatorname{Spec} R$ and every rigidified line bundle $M$ on $C\times_{\operatorname{Spec} R}T$ with the same fibrewise property there is a unique $T\to D.P$ over $\operatorname{Spec} R$ pulling the Poincaré bundle back to a bundle isomorphic to $M$, the pullback along the zero section being isomorphic to the unit bundle. Assume finally that $D.\mathrm{toBase}$ is smooth, proper and geometrically connected. Then there exist types $A$ and $\sigma$ in the same universe as the schemes, a commutative ring structure on $A$, a `SetLike`/`AddSubgroupClass` structure of $\sigma$ over $A$, a grading $\mathcal A\colon\mathbb N\to\sigma$ making $A$ a graded ring, and a morphism $\iota\colon D.P\to\operatorname{Proj}\mathcal A$ which is finite.
--
--   Classically the Jacobian $\mathrm{Pic}^0_{C/R}$ of a pointed smooth proper curve is projective over the base; recorded here is the weaker statement that the representing scheme admits a finite morphism to some $\operatorname{Proj}$ of an $\mathbb N$-graded ring. It is used to produce affine neighbourhoods of finite sets of points on the relative $\mathrm{Pic}^0$ scheme, via the companion result on the existence of an affine open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isFinite_proj_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.exists_isFinite_proj_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase) :
    ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜) (ι : D.P ⟶ Proj 𝒜), IsFinite ι := by sorry
