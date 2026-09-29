-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4697bda1-446d-56a5-a335-cd1e8c9df667
-- title:
--   Sections of L^{⊗ m} as the twist datum φ^*𝒪(m)
-- statement:
--   Let $A$ be a commutative ring, $N,m$ natural numbers, $X$ a scheme, $f\colon X\to\operatorname{Spec}A$ a morphism, and $L$ an object of `X.Modules`. Let $\mathfrak{P}$ be a `ProjPresentation` of $L$ over $f$ of size $N$, that is: global sections $\sigma_i\in\Gamma(L,\top)$ for $i\in\mathrm{Fin}(N+1)$, a morphism $\varphi=\mathfrak{P}.\mathtt{toProj}\colon X\to\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $A$ with $\varphi$ followed by the structure morphism equal to $f$, the requirement that for every $i$ and every open $V$ contained in the chart $\varphi^{-1}D_+(X_i)$ the map $g\mapsto g\cdot\sigma_i|_V$ from $\Gamma(X,V)$ to $\Gamma(L,V)$ is bijective, and the relation $\varphi^{\sharp}(X_j/X_i)\cdot\sigma_i=\sigma_j$ on that chart. Then there is a family of $\Gamma(X,U)$-linear maps $e_U\colon\Gamma(L^{\otimes m},U)\to \mathtt{twistObj}\,f\,\varphi\,m\,U$, indexed by the opens $U$ of $X$, the target consisting of tuples $(g_i)_i$ with $g_i\in\Gamma(X,U\cap\varphi^{-1}D_+(X_i))$ subject to $g_i=\mathtt{frameUnit}\,\varphi\,i\,j^{\,m}\cdot g_j$ on $U\cap\varphi^{-1}D_+(X_i)\cap\varphi^{-1}D_+(X_j)$, such that: (i) for all $U$, all $x\in\Gamma(L^{\otimes m},U)$ and all $i$, the $i$-th component of $e_U(x)$ times the restriction of the global section $\mathtt{tensorPowSection}(\sigma_i)\,m$ of $L^{\otimes m}$ (the $m$-fold tensor power of $\sigma_i$, with $1$ for $m=0$) equals the restriction of $x$, both to $U\cap\varphi^{-1}D_+(X_i)$; (ii) for $U\le U'$ and $x\in\Gamma(L^{\otimes m},U')$, $e_U(x|_U)=\mathtt{twistRes}\,f\,\varphi\,m\,(e_{U'}(x))$; and (iii) $e_U$ is bijective whenever $U\le\varphi^{-1}D_+(X_i)$ for some $i$. Here $L^{\otimes m}$ is the iterated tensor power, with $L^{\otimes 0}$ the unit object.
--
--   This is the chartwise identification of $L^{\otimes m}$ with the pullback $\varphi^*\mathcal{O}(m)$ presented by the cocycle $(X_j/X_i)^m$, written in the frames $\sigma_i^{\otimes m}$; it is the form in which sections of tensor powers of a module presented by global sections are computed. It is used in the computation of Čech complexes and Euler characteristics of twists along the pulled-back standard cover of $\mathbb{P}^N_A$, and in the Hilbert-function statements that rest on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {L : X.Modules}
    (𝔓 : L.ProjPresentation f N) (m : ℕ) :
    ∃ e : ∀ U : X.Opens, Γ(L.tensorPow m, U) →ₗ[Γ(X, U)] ProjSpace.twistObj f 𝔓.toProj m U,
      (∀ (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)),
          ((e U x).val i) •
              (L.tensorPow m).presheaf.map (homOfLE (le_top : U ⊓ ProjSpace.pullbackChart 𝔓.toProj i ≤ ⊤)).op
                (Scheme.Modules.tensorPowSection (𝔓.σ i) m) =
            (L.tensorPow m).presheaf.map (homOfLE (inf_le_left : U ⊓ ProjSpace.pullbackChart 𝔓.toProj i ≤ U)).op x) ∧
      (∀ (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow m, U')),
          e U ((L.tensorPow m).presheaf.map (homOfLE h).op x) = ProjSpace.twistRes f 𝔓.toProj m h (e U' x)) ∧
      (∀ (U : X.Opens) (i : Fin (N + 1)), U ≤ ProjSpace.pullbackChart 𝔓.toProj i → Function.Bijective (e U)) := by sorry
