-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/b09494cd-3357-5737-a6dd-5a11e387f20b
-- title:
--   Sections of L^{⊗ m} as the twist datum of a Proj presentation
-- statement:
--   Let $A$ be a commutative ring, $N,m$ natural numbers, $X$ a scheme, $f : X \to \operatorname{Spec} A$ a morphism, $L$ an $\mathcal O_X$-module, and let $\mathfrak P$ be a `ProjPresentation` of $L$ over $f$ of size $N$: global sections $\sigma_i \in \Gamma(L,\top)$ for $i \in \mathrm{Fin}(N+1)$, a morphism $\varphi = \mathfrak P.\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $A$ whose composite with the structure morphism is $f$, such that on every open $V$ contained in the chart $\varphi^{-1}D_+(X_i)$ the map $g \mapsto g\cdot\sigma_i|_V$ is a bijection $\Gamma(X,V) \to \Gamma(L,V)$, and such that $\varphi^\sharp(X_j/X_i)\cdot\sigma_i = \sigma_j$ on that chart. The assertion is the existence of a family of $\Gamma(X,U)$-linear maps $e_U : \Gamma(L^{\otimes m},U) \to \mathrm{twistObj}\,f\,\varphi\,m\,U$, one for each open $U \subseteq X$, where the target consists of the families $(g_i)_i$ with $g_i \in \Gamma(X, U \cap \varphi^{-1}D_+(X_i))$ satisfying $g_i = \mathrm{frameUnit}(i,j)^m\, g_j$ on $U \cap \varphi^{-1}D_+(X_i) \cap \varphi^{-1}D_+(X_j)$, subject to three conditions: (i) for all $U$, $x$ and $i$, the $i$-th component of $e_U(x)$ times the restriction of the $m$-fold tensor power section $\sigma_i^{\otimes m} \in \Gamma(L^{\otimes m},\top)$ equals the restriction of $x$, both taken to $U \cap \varphi^{-1}D_+(X_i)$; (ii) for $U \le U'$ and $x \in \Gamma(L^{\otimes m},U')$, $e_U(x|_U) = \mathrm{twistRes}(h)(e_{U'}(x))$; (iii) $e_U$ is bijective whenever $U$ is contained in some chart $\varphi^{-1}D_+(X_i)$.
--
--   This is the chartwise description of $L^{\otimes m}$ as $\varphi^{*}\mathcal O_{\mathbb P^N}(m)$ written in the frames $\sigma_i^{\otimes m}$, with transition cocycle $(X_j/X_i)^m$, compatible with restriction and an isomorphism over each chart. It is used in the computations of Euler characteristics of the tensor powers $L^{\otimes m}$ and in the vanishing of higher cohomology for modules finite by sections along a Proj presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
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
