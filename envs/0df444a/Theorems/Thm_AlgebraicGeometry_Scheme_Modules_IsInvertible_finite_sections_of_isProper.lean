-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.finite_sections_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/4efac475-3561-52aa-bc79-0bc88ffe1a9c
-- title:
--   Finiteness of global sections of an invertible sheaf on a proper k-scheme
-- statement:
--   Let $k$ be a field, let $X$ be a scheme, let $f : X \to \operatorname{Spec} k$ be a morphism of schemes which is proper, and let $\mathcal N$ be a sheaf of $\mathcal O_X$-modules which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of $\mathcal N$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules, to the unit sheaf of modules on $U$ (that is, $\mathcal O_U$ itself). Give $\Gamma(X, \mathcal O_X) = \Gamma(X, \top)$ the $k$-algebra structure coming from the ring homomorphism obtained by composing the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} k, \mathcal O) \cong k$ with the map $f^{\sharp}$ on sections over the whole space, and give $\Gamma(\mathcal N, \top)$ the $k$-module structure obtained from its $\Gamma(X, \mathcal O_X)$-module structure by restriction of scalars along the resulting structure map $k \to \Gamma(X, \mathcal O_X)$. The conclusion is that $\Gamma(\mathcal N, \top)$ is a finite $k$-module, i.e. finitely generated and hence a finite-dimensional $k$-vector space.
--
--   This is the degree-zero case of the coherent finiteness theorem for proper morphisms, for a locally free sheaf of rank one over a field. It supplies the finite-dimensionality of spaces of sections used in the construction of closed immersions and stabiliser computations for polarisations, such as [`AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos`](thm.html#AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.finite_sections_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (𝓝 : X.Modules) (h𝓝 : Scheme.Modules.IsInvertible 𝓝) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
    Module.Finite k Γ(𝓝, ⊤) := by sorry
