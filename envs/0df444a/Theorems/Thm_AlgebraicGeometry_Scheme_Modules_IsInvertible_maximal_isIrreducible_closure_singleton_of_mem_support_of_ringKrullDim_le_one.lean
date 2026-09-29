-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/73911498-4199-5fe9-99fa-a76a9ac06ad9
-- title:
--   Codimension-one points of the zero locus of a section
-- statement:
--   Let $X$ be an integral scheme and let $M$ be an object of the category $X.\mathrm{Modules}$ of sheaves of modules on $X$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $s : \mathbb{1}_{X.\mathrm{Modules}} \to M$ be a nonzero morphism from the monoidal unit, i.e. a nonzero global section of $M$, and let `Scheme.Modules.zeroSchemeIdeal s` be the associated ideal sheaf datum on $X$, defined as the infimum of all ideal sheaf data $J$ with $\mathrm{coeffIdeal}(s, U) \le J(U)$ for every affine open $U$, where $\mathrm{coeffIdeal}(s, U)$ is the ideal of $\Gamma(X, U)$ spanned by the coefficients of $s$ over $U$. Assume $x$ is a point lying in the support $D$ of this ideal sheaf datum, and that the local ring $\mathcal{O}_{X,x}$ has Krull dimension at most $1$. Then $\overline{\{x\}}$ is maximal, with respect to inclusion, among the subsets of $X$ that are irreducible and contained in $D$; that is, $\overline{\{x\}}$ is irreducible and contained in $D$, and any irreducible subset of $D$ containing it is contained in $\overline{\{x\}}$.
--
--   This is the statement that a point of the zero locus of a nonzero section of an invertible sheaf at which the local ring has dimension at most one is the generic point of an irreducible component of that zero locus. It feeds into the identification of the zero scheme ideal under pullback in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq), part of the treatment of relative Picard functors and Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) (x : X)
    (hx : x ∈ (Scheme.Modules.zeroSchemeIdeal s).support) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    Maximal (fun C' : Set X => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal s).support) (closure {x}) := by sorry
