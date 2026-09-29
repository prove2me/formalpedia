-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a11bcfac-d445-548f-8d58-8c1015b51ca8
-- title:
--   Constancy of the genus over geometric fibres of a curve
-- statement:
--   Let $R$ be a commutative local Noetherian ring, $C$ a scheme and $c\colon C\to\operatorname{Spec} R$ a proper morphism that is smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R\to C$ composing with $c$ to the identity, and let $\mathfrak F$ be a finite-map datum for $(c,\varepsilon)$: affine opens $U,V$ with $U\sqcup V=\top$, sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ and an $m\in\mathbb N$ such that $U$ is exactly the complement of the image of $\varepsilon$, $U\cap V$ equals both basic opens $C_f$ and $C_g$, the restrictions of $f$ and $g$ have product $1$ on $U\cap V$, $\Gamma(C,U)$ and $\Gamma(C,V)$ are finite over $R[f]$ and $R[g]$ respectively (via evaluation of polynomials), and for every local $R$-algebra $S$ and every $s\in S$ the quotient $S\otimes_R\Gamma(C,U)/(1\otimes f-s\otimes 1)$ is a finite free $S$-module of rank $m$. The assertion is that there is a $g\in\mathbb N$ such that the following holds for all data: an algebraically closed field $k$, a morphism $s\colon\operatorname{Spec} k\to\operatorname{Spec} R$, a field $L$ with a $k$-algebra structure, a `CurveModel` $M$ for $k$ and $L$ (an integral scheme $M.C$ with a proper, relatively one-dimensional smooth structure morphism to $\operatorname{Spec} k$, a ring isomorphism $L\cong$ the function field of $M.C$ over $k$, a bijection from the closed points of $M.C$ to the places of $L/k$ matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open), an isomorphism $e\colon M.C\cong C\times_{\operatorname{Spec} R}\operatorname{Spec} k$ with $e$ followed by the second projection equal to $M.\mathrm{toBase}$, a divisor $K_c$ (a finitely supported $\mathbb Z$-valued function on the places of $L/k$) and a $g'\in\mathbb N$ satisfying $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for every divisor $D$ of $L/k$, where $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$: then $g'=g$.
--
--   This is the constancy of the genus in a smooth proper family of curves over a connected base, in the form needed here: any integer occurring as the genus in a Riemann–Roch identity for a geometric fibre of $c$ is independent of the fibre and of the chosen model. It is used in the construction of the relative Picard scheme, in particular by the results producing finite étale charts of sections from a finite-map datum or over a field, and by the variant of this statement formulated for a connected base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by sorry
