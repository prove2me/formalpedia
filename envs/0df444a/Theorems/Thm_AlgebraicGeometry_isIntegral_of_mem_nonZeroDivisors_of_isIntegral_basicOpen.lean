-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen
-- name    : AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/efe1c604-45c3-5657-ac88-6b6a5e04d510
-- title:
--   Integrality descends from a basic open of a regular section
-- statement:
--   Let $Y$ be a scheme and let $p \in \Gamma(Y, \mathcal{O}_Y)$ be a global section. Assume that for every open subset $U$ of $Y$ which is an affine open, the restriction of $p$ along the inclusion $U \subseteq \top$, i.e. the image of $p$ under the presheaf map attached to $U \le \top$, lies in the non-zero-divisors of the ring $\Gamma(Y, U)$. Assume further that the open subscheme of $Y$ determined by the basic open set $Y_p = \{p \neq 0\}$ is an integral scheme, that is, its underlying topological space is irreducible (in particular non-empty) and its structure sheaf is reduced. Then $Y$ itself is integral: the underlying space of $Y$ is irreducible and $Y$ is reduced. No Noetherian, quasi-compact or finite-type hypothesis is imposed, and the section $p$ is not assumed to be a non-zero-divisor in any stronger sense than affine-locally.
--
--   This is the standard criterion by which integrality of a scheme is checked on the locus where a regular section is invertible; the typical application is to a scheme flat over a discrete valuation ring with uniformiser $\varpi$, whose generic fibre is the basic open set of $\varpi$. In this development it is used to establish integrality of pullbacks of models of modular curves, for instance by [`ModularCurve.DRModel.isIntegral_pullback_toBase`](thm.html#ModularCurve.DRModel.isIntegral_pullback_toBase) and [`ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion`](thm.html#ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [hint : IsIntegral (Y.basicOpen p : Scheme)] : IsIntegral Y := by sorry
