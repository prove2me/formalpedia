-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5806bdb1-9ca5-57f3-b918-e67c0acee7fc
-- title:
--   Sections of a locally trivial module have base-change rank one
-- statement:
--   Let $X$ be a scheme and let $M$ be an object of `X.Modules`, i.e. a sheaf of modules over the sheaf of rings of $X$. Assume $M$ is locally trivial in the following sense: for every point $x$ of $X$ there is an open subset $V \subseteq X$ with $x \in V$ such that the pullback of $M$ along the open immersion $V \hookrightarrow X$ is isomorphic, as a sheaf of modules on $V$, to the unit object `SheafOfModules.unit` of the sheaf of rings of $V$ — that is, $M$ restricted to $V$ is isomorphic to the structure sheaf of $V$. Let $U$ be an affine open of $X$, so that $\Gamma(X, U)$ is the ring of sections of the structure sheaf over $U$ and $\Gamma(M, U)$ the $\Gamma(X, U)$-module of sections of $M$ over $U$. Let $K$ be a field (in the same universe) equipped with an algebra structure over $\Gamma(X, U)$; no further hypothesis on this algebra structure is imposed. Then the $K$-dimension of $K \otimes_{\Gamma(X, U)} \Gamma(M, U)$ equals $1$.
--
--   This is the rank-one half of the classical dictionary between invertible sheaves on a scheme and rank-one finitely generated projective modules over the sections ring of an affine open: together with the finiteness and projectivity of $\Gamma(M, U)$ it says that the sections of a line bundle over an affine open form an invertible module. It is used in the treatment of invertible sheaves of modules, in particular when recognising invertibility through descent data and when comparing relative effective Cartier divisors with line bundle isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (K : Type u) [Field K] [Algebra Γ(X, U.1) K] :
    Module.finrank K (K ⊗[Γ(X, U.1)] Γ(M, U.1)) = 1 := by sorry
