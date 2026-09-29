-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/00dab3ce-a3a3-58e3-8f31-6e4f27f7b46b
-- title:
--   Finite étale descent of a relative Pic⁰ representing scheme
-- statement:
--   Let $R$ be a reduced Noetherian ring, $c : C \to \operatorname{Spec} R$ a proper morphism, smooth of relative dimension one and with geometrically integral fibres, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Assume $(c,\varepsilon)$ admits `FiniteMapData` of arbitrarily large degree: for each $m_0$ there are two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose restrictions to $U \cap V = C_f = C_g$ are mutually inverse, with $R[f] \to \Gamma(C,U)$ and $R[g] \to \Gamma(C,V)$ finite, and such that for every local $R$-algebra $S$ and $s \in S$ the quotient $S \otimes_R \Gamma(C,U)$ by $(1 \otimes f - s \otimes 1)$ is free of rank $m \ge m_0$ over $S$. Let $R'$ be a finite étale faithfully flat $R$-algebra, $c' : C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$ the base change and $\varepsilon'$ the induced section. Suppose given a pointed $R'$-scheme $D'$ (a scheme $D'.P$, a structure morphism $D'.\mathrm{toBase}$ to $\operatorname{Spec} R'$ and a section of it) together with data exhibiting $D'$ as representing the relative Picard functor of $(c', \varepsilon')$ cut out by the condition `algEquivZeroCut`: a rigidified line bundle on $C' \times_{R'} D'.P$ satisfying that condition such that for every $T \to \operatorname{Spec} R'$ and every rigidified line bundle $M$ on $C' \times_{R'} T$ all of whose geometric fibres, over all algebraically closed fields, are algebraically equivalent to zero, there is a unique $T \to D'.P$ over $\operatorname{Spec} R'$ pulling the Poincaré bundle back to a bundle isomorphic to $M$, the pullback along the zero section being trivial. Assume further that $D'.\mathrm{toBase}$ is smooth, proper and geometrically connected, and that every finite set of points of $D'.P$ lies in an affine open. Then there exists a pointed $R$-scheme $D$ which likewise represents the `algEquivZeroCut` part of the rigidified relative Picard functor of $(c,\varepsilon)$, whose structure morphism $D.\mathrm{toBase}$ is smooth, proper and geometrically connected, and an isomorphism $e$ from $D.P \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ onto $D'.P$ compatible with the two morphisms to $\operatorname{Spec} R'$.
--
--   This is the faithfully flat (finite étale) descent step for the relative Jacobian: a representing scheme for the fibrewise-algebraically-trivial part of the rigidified relative Picard functor of a smooth proper relative curve descends from $R'$ to $R$, together with its smoothness, properness and fibral connectedness. It is the edition of the descent theorem keyed to a reduced base and a chart-wise finite map datum, and it feeds the construction of the relative Jacobian over a discrete valuation ring and the analysis of $\mathrm{Pic}^0$ of the special fibre of the two-chart model of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (baseChange R c R'))
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) D')
    (hsm : Smooth D'.toBase) (hpr : IsProper D'.toBase) (hgc : GeometricallyConnected D'.toBase)
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        ∃ e : pullback D.toBase (specMap R R') ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd D.toBase (specMap R R') := by sorry
