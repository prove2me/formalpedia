-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
-- name    : AlgebraicGeometry.RelPicard.finrank_H0_unit_fibre_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/16ad9c7b-0dda-5b49-b982-f9ef9382a5a2
-- title:
--   Geometric fibres of smooth proper curves have h⁰(𝒪)=1
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a morphism which is proper, smooth of relative dimension $1$, and geometrically integral (the instances `IsProper c`, `SmoothOfRelativeDimension 1 c`, `GeometricallyIntegral c`). Let $k$ be an algebraically closed field and $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a morphism, so that the pullback $C_s=C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ is formed, with structure map the second projection `pullback.snd c s` to $\operatorname{Spec}k$. Let $\mathcal V$ be a `TwoAffineOpenCover` of $C_s$, that is, two opens $U_0,U_1$ of $C_s$, both affine, with $U_0\sqcup U_1=\top$ and with $U_0\sqcap U_1$ affine as well. Take $M$ to be the monoidal unit of the category of modules on $C_s$, i.e. the structure sheaf. The associated two-chart Čech data consist of the sections $\Gamma(M,U_0)$, $\Gamma(M,U_1)$, $\Gamma(M,U_0\sqcap U_1)$, regarded as $k$-modules via the structure map, together with the two restriction maps $r_0,r_1$ to the intersection; its $H^0$ is the kernel of $(m_0,m_1)\mapsto r_1(m_1)-r_0(m_0)$, i.e. the $k$-module of pairs of sections agreeing on $U_0\sqcap U_1$. The assertion is that this $k$-module has finrank $1$.
--
--   This is the statement $h^0(C_s,\mathcal O_{C_s})=1$ for a geometric fibre of a smooth proper relative curve with geometrically integral fibres, in the two-chart Čech presentation used throughout the relative Picard machinery. It is used in the construction and rigidification of relative line bundles and divisors, for instance in [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre) and in the comparison of $H^1$ of a line bundle with $H^1$ of the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelPicard.finrank_H0_unit_fibre_eq_one
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒱 : (pullback c s).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 = 1 := by sorry
