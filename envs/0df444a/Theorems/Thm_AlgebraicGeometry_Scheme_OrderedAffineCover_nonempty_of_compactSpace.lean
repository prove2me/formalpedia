-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.nonempty_of_compactSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/fd4c9213-46d7-5a3a-960c-bca9dec9f8ee
-- title:
--   Compact schemes admit ordered finite affine open covers
-- statement:
--   Let $V$ be a scheme (in universe $u$) whose underlying topological space is compact. The assertion is that the type `V.OrderedAffineCover` is nonempty, i.e. that there exists a datum consisting of: an index type $\iota$ in the universe $u$, equipped with a `Fintype` structure and a linear order; a family $U \colon \iota \to V.Opens$ of open subsets of $V$; a proof that $U i$ is an affine open of $V$ for every $i$; and a proof that $\bigvee_{i} U i = \top$, the supremum being taken in the lattice of opens of $V$. Thus $V$ is covered by finitely many affine opens indexed by a finite linearly ordered set. Note that the linear order on the index set carries no compatibility requirement with the family $U$: it is extra structure attached to $\iota$, and no injectivity of $i \mapsto U i$ is demanded either.
--
--   This is the standard statement that a quasi-compact scheme has a finite affine open cover, packaged so that the index set additionally carries a linear order — the order being what permits the formation of alternating Čech cochains for the cover. It is invoked wherever a Čech computation on a compact scheme is set up, for instance in the results on polarisations about finite-rank spaces of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.nonempty_of_compactSpace (V : Scheme.{u}) [CompactSpace V] : Nonempty V.OrderedAffineCover := by sorry
