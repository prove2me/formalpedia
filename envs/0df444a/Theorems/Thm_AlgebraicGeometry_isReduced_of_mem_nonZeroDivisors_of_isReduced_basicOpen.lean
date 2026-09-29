-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
-- name    : AlgebraicGeometry.isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9092ea15-6feb-5e26-9c9e-5132b658e5a6
-- title:
--   Reducedness descends from a basic open locus of a regular section
-- statement:
--   Let $Y$ be a scheme and let $p \in \Gamma(Y, \mathcal{O}_Y)$ be a section over the whole space. Assume that for every open subset $U \subseteq Y$ which is an affine open, the restriction of $p$ to $U$, that is the image of $p$ under the map $\Gamma(Y, \top) \to \Gamma(Y, U)$ of the structure presheaf induced by the inclusion $U \le \top$, is a non-zero-divisor in the ring $\Gamma(Y, U)$. Assume moreover that the open subscheme of $Y$ associated with the basic open set $Y_p = \{p \neq 0\}$ of $p$ is a reduced scheme. The conclusion is that $Y$ itself is a reduced scheme, i.e. satisfies Mathlib's `IsReduced` predicate for schemes (every ring of sections over an open is reduced).
--
--   This is the reducedness half of the standard criterion that a scheme which is torsion-free with respect to a global section and reduced on the locus where that section is invertible is reduced; in the classical setting $p$ is a uniformiser of a discrete valuation ring over which $Y$ is flat, so that reducedness of the generic fibre propagates to $Y$. It is used in the proof of the corresponding integrality statement [`AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen`](thm.html#AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

theorem AlgebraicGeometry.isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
    {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [IsReduced (Y.basicOpen p : Scheme)] : IsReduced Y := by sorry
