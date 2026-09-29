-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_bijective_algebraMap_sections_baseChange_of_finiteMapData
-- name    : AlgebraicGeometry.SmoothProperCurve.bijective_algebraMap_sections_baseChange_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e5ad0d74-6b75-559a-8a22-1edb30924a39
-- title:
--   A→Γ(C_A,𝒪) bijective, from finite-map data
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Assume that for every $m_0\in\mathbb N$ there is a datum $\mathfrak F$ of type `FiniteMapData` for $c$ and $\varepsilon$ with $m_0\le\mathfrak F.m$; such a datum consists of two affine opens $U,V\subseteq C$ with $U\sqcup V=\top$ and $U\sqcap V$ affine, sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ and an integer $m$, subject to: a point lies in $U$ exactly when it is not in the image of $\varepsilon$; $U\sqcap V$ equals both the basic open of $f$ and the basic open of $g$; the restrictions of $f$ and $g$ to $U\sqcap V$ have product $1$; the $R$-algebra maps $R[X]\to\Gamma(C,U)$, $X\mapsto f$, and $R[X]\to\Gamma(C,V)$, $X\mapsto g$, for the $R$-algebra structures induced by $c$, are finite; and for every local $R$-algebra $S$ and every $s\in S$ the quotient $(S\otimes_R\Gamma(C,U))/(1\otimes f-s\otimes 1)$ is a finite free $S$-module of rank $m$. Then for every commutative $R$-algebra $A$, the structure map $A\to\Gamma\bigl(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top\bigr)$, for the $A$-algebra structure on global sections induced by the projection to $\operatorname{Spec}A$, is bijective.
--
--   This is the statement that $\mathcal O\to c_*\mathcal O_C$ is an isomorphism universally, i.e. after arbitrary base change, for a proper smooth curve with geometrically integral fibres, in the edition that assumes a reduced base together with finite-map data of unbounded degree. It is used in the construction of the relative Picard functor, namely in the proofs that the relevant sub-Picard presheaf satisfies the sheaf condition for the finite étale and for the Zariski topologies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_bijective_algebraMap_sections_baseChange_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.bijective_algebraMap_sections_baseChange_of_finiteMapData
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)) := by sorry
