-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/5ce8b7fe-d581-56cb-8b5b-3f703e5c54c3
-- title:
--   Radical ideal sheaf with pairwise disjoint support splits as a product
-- statement:
--   Let $Y$ be a scheme and $\iota$ a finite index type, and let $Z : \iota \to \mathrm{Closeds}\,Y$ be a family of closed subsets of the underlying space of $Y$ which is pairwise disjoint, i.e. $Z_i$ and $Z_j$ are disjoint for all $i \neq j$. Let $J$ be a quasi-coherent ideal sheaf on $Y$ (an element of `Y.IdealSheafData`) satisfying $J.\mathrm{radical} = J$, so that the closed subscheme cut out by $J$ is reduced, and assume that the support of $J$ is the supremum of the $Z_i$ in the lattice of closed subsets, $\mathrm{supp}\,J = \bigsqcup_i Z_i$ (that is, the union of the $Z_i$). The conclusion is the equality, in the commutative monoid of quasi-coherent ideal sheaves on $Y$ under multiplication, $$\prod_{i} \mathcal{I}(Z_i) = J,$$ where $\mathcal{I}(Z) =$ `Scheme.IdealSheafData.vanishingIdeal Z` is the largest quasi-coherent ideal sheaf with vanishing locus $Z$, i.e. the ideal sheaf of the reduced induced closed subscheme structure on $Z$, and the product is taken over all of $\iota$.
--
--   This is the scheme-theoretic form of the statement that a reduced closed subscheme whose underlying closed set is a finite disjoint union decomposes, on the level of ideal sheaves, as the product of the vanishing ideals of the pieces; it is the global input used when identifying the divisor of a uniformiser on a regular model of a curve over a discrete valuation ring with the sum of its fibre components. It is cited in the construction of Deligne–Rapoport-style models and charts for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
    {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (Z : ι → Closeds Y)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    (J : Y.IdealSheafData) (hrad : J.radical = J) (hsupp : J.support = ⨆ i, Z i) :
    ∏ i, Scheme.IdealSheafData.vanishingIdeal (Z i) = J := by sorry
