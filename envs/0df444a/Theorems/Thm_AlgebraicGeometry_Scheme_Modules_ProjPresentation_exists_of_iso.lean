-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/241df6ce-75a9-54a6-b267-0f889f46d5e6
-- title:
--   Transport of a P^N-presentation along a module isomorphism
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ and $M'$ two sheaves of $\mathcal{O}_X$-modules (objects of `X.Modules`), and $N$ a natural number. Suppose given $\mathfrak{P} :$ `M.ProjPresentation f N`, that is: global sections $\sigma_i \in \Gamma(M, \top)$ for $i \in \{0,\dots,N\}$, a morphism `toProj` from $X$ to $\operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$, such that `toProj` followed by the structure morphism $\mathbb{P}^N_R \to \operatorname{Spec} R$ equals $f$, such that for every $i$ and every open $V \subseteq X$ contained in the preimage under `toProj` of the basic open $D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective, and such that for all $i,j$ the pullback along `toProj` of the section of $\mathcal{O}$ on $D_+(x_i)$ given by $x_j/x_i$ in the degree-zero localisation away from $x_i$ multiplies the restriction of $\sigma_i$ to the preimage of $D_+(x_i)$ into the restriction of $\sigma_j$ there. Let $e : M \cong M'$ be an isomorphism in `X.Modules`. Then there exists $\mathfrak{P}' :$ `M'.ProjPresentation f N` whose morphism to $\operatorname{Proj}$ is the same as that of $\mathfrak{P}$ and whose sections satisfy $\sigma'_i = e_{\top}(\sigma_i)$ for all $i$, where $e_{\top}$ is the map on global sections induced by $e$.
--
--   This is the data-level invariance, under isomorphism of the module, of the classical description of a morphism to $\mathbb{P}^N_R$ by $N+1$ sections framing an invertible module on the preimages of the standard charts, with the transition relations $\varphi^{\sharp}(x_j/x_i)\,\sigma_i = \sigma_j$. It is used when the same morphism must be presented by modules arising from different constructions, and is cited in the treatment of framed polarised abelian schemes, for instance in the results on immersions into projective space and on reframing and pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') :
    ∃ 𝔓' : M'.ProjPresentation f N, 𝔓'.toProj = 𝔓.toProj ∧ ∀ i, 𝔓'.σ i = (e.hom.app ⊤) (𝔓.σ i) := by sorry
