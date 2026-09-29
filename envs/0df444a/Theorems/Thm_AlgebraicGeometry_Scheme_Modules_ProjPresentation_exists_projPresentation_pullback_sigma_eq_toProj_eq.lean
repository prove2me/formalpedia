-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/f51c2ac1-e9e7-5d77-9108-ed0b0fe93297
-- title:
--   Pullback of a P^N_R-presentation along a morphism of schemes
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $X'$ be schemes, let $f : X \to \operatorname{Spec} R$ be a morphism, let $p : X' \to X$ be an arbitrary morphism of schemes, let $M$ be an $\mathcal{O}_X$-module (an object of `X.Modules`), let $N$ be a natural number, and let $\mathfrak{P}$ be a `ProjPresentation` of $M$ over $f$ of size $N$, that is: global sections $\sigma_i \in \Gamma(M,\top)$ for $i \in \mathrm{Fin}(N+1)$, a morphism $\tau = \mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of homogeneous components of $R[X_0,\dots,X_N]$ with $\tau$ followed by the structure morphism `ProjSpace.π R N` equal to $f$, such that for every $i$ and every open $V \le \tau^{-1}D_+(X_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective, and such that for all $i,j$ the section obtained by applying $\tau^\sharp$ on $D_+(X_i)$ to the class $X_j/X_i$ in the degree-zero away algebra satisfies $\tau^\sharp(X_j/X_i) \cdot (\sigma_i|_{\tau^{-1}D_+(X_i)}) = \sigma_j|_{\tau^{-1}D_+(X_i)}$. Then there exists a `ProjPresentation` $\mathfrak{P}'$ of the pulled-back module $(\mathtt{Scheme.Modules.pullback}\ p).\mathrm{obj}\ M$ over the composite $p$ followed by $f$, again of size $N$, whose sections are $\mathfrak{P}'.\sigma_i = \eta(\sigma_i)$, the image of $\sigma_i$ under the component at $\top$ of the unit of the adjunction `Scheme.Modules.pullbackPushforwardAdjunction p` at $M$, and whose morphism to $\operatorname{Proj}$ is $p$ followed by $\tau$.
--
--   This is the base-change compatibility of the notion of a presentation of a morphism to $\mathbb{P}^N_R$ by $N+1$ global sections of a line-bundle-like module: such data pull back along any morphism of schemes, with the pulled-back sections and the composed morphism to projective space. It is used repeatedly in the treatment of framed polarised abelian schemes, for instance when comparing frames and ratios after base change and when producing immersions into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X)
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : ((Scheme.Modules.pullback p).obj M).ProjPresentation (p ≫ f) N,
      (∀ i, 𝔓'.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) (𝔓.σ i)) ∧
      𝔓'.toProj = p ≫ 𝔓.toProj := by sorry
