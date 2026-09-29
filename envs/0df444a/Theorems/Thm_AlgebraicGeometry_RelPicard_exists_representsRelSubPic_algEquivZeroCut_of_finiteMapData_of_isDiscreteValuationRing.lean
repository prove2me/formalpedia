-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/57e55719-1964-5688-9ea7-3e3b649b6af4
-- title:
--   Relative Pic⁰ representable over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), let $c\colon C\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity. Assume that for every $m_0\in\mathbb{N}$ there is a datum `FiniteMapData` for $(c,\varepsilon)$ with invariant $m\ge m_0$ satisfying `LevelSetsGenericallyEtale`: affine opens $U,V$ with $U\sqcup V=C$, $U$ the complement of the image of $\varepsilon$, sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ with $U\cap V=C_f=C_g$ and $f\cdot g=1$ there, $\Gamma(C,U)$ finite over $R[f]$ and $\Gamma(C,V)$ finite over $R[g]$, such that for every local $R$-algebra $S$ and $s\in S$ the quotient $S\otimes_R\Gamma(C,U)$ by $(1\otimes f-s\otimes 1)$ is finite free of rank $m$ over $S$, and such that for some polynomial over $R$ with a unit coefficient, that quotient is étale over $S$ whenever the polynomial evaluated at $s$ is a unit (for local $R$-algebras with local structure map). Then there exist a scheme $P$ with a structure morphism $P\to\operatorname{Spec}R$ and a section of it (a `RelativePic0Designation`), together with a $\varepsilon$-rigidified invertible module $\mathcal{P}$ on $C\times_R P$ whose restriction to every geometric fibre is algebraically equivalent to zero, such that for every $R$-scheme $T$ and every $\varepsilon$-rigidified invertible module $M$ on $C\times_R T$ with the same fibrewise condition there is a unique $R$-morphism $T\to P$ pulling $\mathcal{P}$ back to a module isomorphic to $M$, the section of $P$ pulling $\mathcal{P}$ back to the unit module; moreover $P\to\operatorname{Spec}R$ is smooth, proper and geometrically connected.
--
--   This is the existence of the relative Jacobian $\operatorname{Pic}^0_{C/R,\varepsilon}$ of a pointed smooth proper curve with geometrically integral fibres over a discrete valuation ring, phrased through its universal property and with smoothness, properness and geometric connectedness of the structure morphism. It is the form in which the Jacobian is used for modular curves over local bases, being cited in the construction of level models of $J_0$ and $X_H$ and in the comparison of their cotangent spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
