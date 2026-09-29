-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle
-- name    : AlgebraicGeometry.RelPicard.isInvertible_thetaBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/6a191bcb-ad7f-5c01-a67d-65b42cc95a14
-- title:
--   Invertibility of the theta bundle of a relative curve
-- statement:
--   Let $R$ be a Noetherian commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper morphism that is smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Assume `h𝔉`: for every $m_0\in\mathbb N$ there is a datum `SmoothProperCurve.FiniteMapData c ε` whose numerical invariant `m` is at least $m_0$. Let $t\colon T\to\operatorname{Spec}R$ be locally of finite type and let $M$ be a rigidified line bundle for $(c,\varepsilon,t)$, that is, a module `M.L` on the fibre product of $c$ and $t$ which is invertible (locally isomorphic to the unit module) together with a trivialisation of its pullback along the tautological section `rigSection c t ε`. Fix $r,n\in\mathbb N$ and write $F=M.L\otimes\,$`sectionTwist c ε t r`, where `sectionTwist c ε t r` is the dual of the module attached to the $r$-th power of the kernel ideal sheaf of `rigSection c t ε`. Assume `hfib`: for every field $k$, every $s\colon\operatorname{Spec}k\to T$ and every cover of the fibre $\operatorname{pullback}(\operatorname{pullback.snd} c\,t)\,s$ by two affine opens with affine intersection, the two-chart Čech complex of the pullback of $F$ to that fibre, taken relative to the structure morphism `fibreAt c t s`, has subsingleton $H^1$ and $\dim_k H^0=n$. Then `thetaBundle c ε t M r n`, the dual of the $n$-th determinant of `picardBundle c ε t M (sectionTwist c ε t r)`, is invertible: every point of $T$ has an open neighbourhood on which this module is isomorphic to the unit module.
--
--   This is the statement that the theta bundle attached to a family of line bundles on a pointed smooth proper relative curve, the dual determinant of the associated Picard bundle, is a line bundle on the base. It is used in the construction of the relative Picard scheme, being cited in the production of a finite projection for the functor representing the relevant sub-Picard locus and in the statement about finiteness by sections of tensor powers of the theta bundle over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.isInvertible_thetaBundle
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n) :
    Scheme.Modules.IsInvertible (thetaBundle c ε t M r n) := by sorry
