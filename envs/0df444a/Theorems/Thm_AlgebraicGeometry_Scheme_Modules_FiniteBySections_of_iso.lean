-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/978ee6a3-1c56-5d17-98c8-842f6d460c62
-- title:
--   Invariance of `FiniteBySections` under isomorphism of modules
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, and $M, M'$ two objects of `X.Modules`. Given an isomorphism $e : M \cong M'$ in `X.Modules` and the hypothesis that $M$ satisfies `FiniteBySections` with respect to $f$, the conclusion is that $M'$ satisfies `FiniteBySections` with respect to $f$. Here `M.FiniteBySections f` asserts the existence of an $N \in \mathbb{N}$ and of a `ProjPresentation` $\mathfrak{P}$ of $M$ over $f$ of size $N$ whose morphism $\mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $R$ is finite (`IsFinite`). Such a presentation consists of: global sections $\sigma_i \in \Gamma(M, \top)$ indexed by $i \in \mathrm{Fin}(N+1)$; a morphism $\mathrm{toProj}$ as above whose composite with the structure morphism `ProjSpace.π R N` to $\operatorname{Spec} R$ is $f$; the frame condition that for each $i$ and each open $V \le \mathrm{toProj}^{-1}(D(X_i))$ the map $\Gamma(X, V) \to \Gamma(M, V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective; and the ratio condition that for all $i, j$ the pullback along $\mathrm{toProj}$ of the section $X_j / X_i$ of $\mathcal{O}$ on $D(X_i)$, acting on $\sigma_i$ restricted to $\mathrm{toProj}^{-1}(D(X_i))$, equals $\sigma_j$ restricted to that open.
--
--   This is the transport of the notion "finite by sections" — a finite morphism to projective space over $R$ presented by finitely many global sections of a module — along an isomorphism of the module. It is used wherever a module, typically a line bundle, is only determined up to isomorphism, for instance after base change or after passing to a tensor power, and is cited in the construction of finite morphisms to projective space from relative Picard data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} (e : M ≅ M')
    (hM : M.FiniteBySections f) : M'.FiniteBySections f := by sorry
