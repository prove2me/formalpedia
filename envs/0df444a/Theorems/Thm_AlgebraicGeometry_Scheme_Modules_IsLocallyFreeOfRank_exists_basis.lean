-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
-- name    : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/91271a01-250b-5989-b0ff-83b54ffdc980
-- title:
--   Local bases of sections for a locally free sheaf
-- statement:
--   Let $X$ be a scheme, $n$ a natural number and $M$ an object of $X.\mathrm{Modules}$, i.e. a sheaf of modules over the structure sheaf of $X$. Assume $M$ is locally free of rank $n$ in the sense of the project's predicate `IsLocallyFreeOfRank`: for every point of $X$ there is an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules on $U$, to the free sheaf of modules on the index type $\mathrm{ULift}(\mathrm{Fin}\,n)$. Let $x$ be a point of $X$. Then there exist an open subset $V$ of $X$ containing $x$ and a family $e : \mathrm{Fin}\,n \to \Gamma(M, V)$ of sections of $M$ over $V$ such that for every open subset $W$ of $X$ with $W \le V$ there is a basis $b$ of the $\Gamma(X, W)$-module $\Gamma(M, W)$ indexed by $\mathrm{Fin}\,n$ whose $i$-th member is the image of $e_i$ under the restriction map $\Gamma(M, V) \to \Gamma(M, W)$ of the presheaf of $M$. Thus the restrictions $e_i|_W$ form a $\Gamma(X,W)$-basis of $\Gamma(M,W)$ simultaneously for all opens $W \subseteq V$.
--
--   This is the standard translation of local freeness of rank $n$ into the existence of a local frame: $n$ sections over a neighbourhood of a given point whose restrictions form a basis of the sections over every smaller open. It is used throughout the project's local computations with locally free sheaves, for instance in the construction of frames along closed immersions and in criteria for a map of locally free sheaves to be an isomorphism in terms of the vanishing of a determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis
    {X : Scheme.{u}} {n : ℕ} {M : X.Modules} (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by sorry
