-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
-- name    : AlgebraicGeometry.isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d5a9738d-3627-5cf0-8047-bd0f2ee8012b
-- title:
--   Square-zero thickenings of affine schemes are affine
-- statement:
--   Let $X_0$ and $X$ be schemes (in a fixed universe) and let $i \colon X_0 \to X$ be a morphism of schemes which is a closed immersion, and suppose $X_0$ is affine. Write $i.\mathrm{ker}$ for the kernel ideal sheaf of $i$, that is the quasi-coherent ideal sheaf $\mathcal I = \ker(\mathcal O_X \to i_*\mathcal O_{X_0})$ on $X$, and assume that its square vanishes, $\mathcal I \cdot \mathcal I = \bot$, the product being taken in the lattice-ordered monoid of ideal sheaves on $X$ and $\bot$ being the zero ideal sheaf. The conclusion is that $X$ is itself affine. Thus a scheme which is a first-order (square-zero) thickening of an affine closed subscheme is affine; no separate quasi-compactness or separatedness hypothesis on $X$ is imposed, these being consequences of $i$ being a closed immersion with nilpotent kernel ideal.
--
--   This is the square-zero case of the standard criterion that a scheme admitting a closed immersion from an affine scheme with nilpotent kernel ideal is affine (EGA I/II; cf. the Stacks Project's characterisation of affine schemes). It is used to derive the general nilpotent case, [`AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isNilpotent_ker`](thm.html#AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isNilpotent_ker), by induction on the order of nilpotence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [IsAffine X₀]
    (h : i.ker * i.ker = ⊥) : IsAffine X := by sorry
