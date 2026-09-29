-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/56aff266-91dc-5ab1-9f84-cd1e8df75cd3
-- title:
--   Reducedness of the vanishing-ideal subscheme, and killing of the ideal
-- statement:
--   Let $X$ be a scheme and let $Z$ be a closed subset of the underlying topological space of $X$, given as an element of `TopologicalSpace.Closeds X`. Write `vanishingIdeal Z` for the quasi-coherent ideal sheaf data on $X$ whose ideal over an affine open $U$ is the vanishing ideal, in $\Gamma(X, U)$, of the subset of $\operatorname{Spec}\Gamma(X,U)$ corresponding to $Z \cap U$, and let `(vanishingIdeal Z).subscheme` be the closed subscheme of $X$ it cuts out. The theorem asserts two things at once. First, `(vanishingIdeal Z).subscheme` is a reduced scheme. Second, for every scheme $T$ (in the same universe) which is reduced and every morphism of schemes $f : T \to X$ whose set-theoretic range is contained in $Z$, one has `vanishingIdeal Z ≤ f.ker`, i.e. the ideal sheaf of $Z$ is contained, in the lattice of ideal sheaf data on $X$, in the kernel ideal sheaf of $f$. The statement stops at this containment: the resulting unique factorisation of $f$ through the closed immersion `(vanishingIdeal Z).subschemeι` is not part of the conclusion.
--
--   Together the two assertions are the existence of the reduced induced closed subscheme structure on a closed subset of a scheme, with the containment in the second part being exactly what is needed for its universal property; the factorisation itself is recorded separately in [`AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced`](thm.html#AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced). It is used in the scheme-theoretic infrastructure of the formalisation, for instance in results on irreducible closed subschemes and Krull dimension and in an affineness criterion along a cover by closed immersions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  AlgebraicGeometry.Scheme.IdealSheafData

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
    {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme ∧
      ∀ {T : Scheme.{u}} [IsReduced T] (f : T ⟶ X), Set.range f ⊆ Z →
        vanishingIdeal Z ≤ f.ker := by sorry
