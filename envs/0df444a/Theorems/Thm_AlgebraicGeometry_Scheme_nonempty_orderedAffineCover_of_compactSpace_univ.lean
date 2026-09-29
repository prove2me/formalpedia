-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
-- name    : AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/1a54ed60-94f6-5f43-b7d4-b992c815df99
-- title:
--   Quasi-compact schemes admit finite ordered affine covers
-- statement:
--   Let $X$ be a scheme, in any universe $u$, whose underlying topological space is compact. The assertion is that the type `X.OrderedAffineCover` is nonempty, i.e. that there exists a datum consisting of: an index type $\iota$ in the universe $u$ equipped with a `Fintype` structure and a linear order; a family $U : \iota \to X.\mathrm{Opens}$ of open subschemes of $X$; a proof that $U_i$ is an affine open of $X$ for every $i$; and a proof that $\bigsqcup_i U_i = \top$, the supremum being taken in the lattice of opens of $X$. Thus $X$ is covered by finitely many affine opens indexed by a finite linearly ordered type. Note that the linear order carries no compatibility requirement with the family $U$; it is only the extra combinatorial datum needed to form alternating Čech complexes. The statement is existential: no particular cover, index type or ordering is specified.
--
--   This is the standard fact that a quasi-compact scheme is a finite union of affine opens, packaged together with a linear ordering of the index set so that alternating Čech complexes can be formed. It is used in the Čech-theoretic part of the development for proper schemes over complete Noetherian rings, for instance by the coherence and formal-splitting statements for $\mathcal{O}$-module presheaves and by the local-section comparison result for modules on schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ
    (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by sorry
