-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
-- name    : AlgebraicGeometry.RelPicard.isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/afb24bf1-2244-5a23-b9f0-2cd449114d53
-- title:
--   Properness and geometric connectedness of a representing Pic⁰
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c : C \to \operatorname{Spec} R$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume: (i) for every $m_0 \in \mathbb{N}$ there is a datum `SmoothProperCurve.FiniteMapData c ε` with invariant $m \ge m_0$ — that is, a cover of $C$ by two affine opens $U, V$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ cutting out $U \cap V$ as a basic open set and inverse to each other there, with $f$ and $g$ finite over $R[X]$ and all level sets of $f$ free of rank $m$ over local $R$-algebras; (ii) a natural number $g$ such that for every algebraically closed field $k$, every $k$-point $s$ of $\operatorname{Spec} R$, every field extension $L/k$, every curve model $M$ of $L/k$ together with an isomorphism $M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ commuting with the structure maps to $\operatorname{Spec} k$, every divisor $K_c$ on $M$ and every $g'$: if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ (where $\ell$ is the $k$-dimension of the Riemann–Roch space), then $g' = g$. Let $D$ consist of a scheme $P$ with structure morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a zero section, and suppose $D.\mathrm{toBase}$ is locally of finite type. Suppose $h$ exhibits $D$ as representing the subfunctor of the relative Picard functor of $(c,\varepsilon)$ cut out by fibrewise algebraic equivalence to zero: there is a rigidified invertible module (Poincaré bundle) on $C \times_R P$ all of whose geometric fibres are algebraically equivalent to zero, such that for every $R$-scheme $T$ and every rigidified invertible module on $C \times_R T$ with the same fibrewise property there is a unique $R$-morphism $T \to P$ pulling the Poincaré bundle back to it, and the pullback along the zero section is the unit. Then $D.\mathrm{toBase}$ is proper and geometrically connected.
--
--   This is the geometric half of the construction of the Jacobian of a pointed smooth proper relative curve: once a scheme representing $\operatorname{Pic}^0_{C/R,\varepsilon}$ is in hand, it is a proper $R$-scheme with geometrically connected fibres. It is used in the existence theorem for such representing schemes over reduced bases, in its base-change form over a field, and in the construction of Abel–Jacobi points on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
