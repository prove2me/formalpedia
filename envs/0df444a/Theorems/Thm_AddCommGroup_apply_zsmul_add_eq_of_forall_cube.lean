-- Prove2me | Theorems.Thm_AddCommGroup_apply_zsmul_add_eq_of_forall_cube
-- name    : AddCommGroup.apply_zsmul_add_eq_of_forall_cube
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6ea16fa2-2865-58a8-8915-617902d40450
-- title:
--   Cube identity forces quadratic behaviour along lines
-- statement:
--   Let $M$ and $N$ be additive abelian groups and let $\Lambda \colon M \to N$ be an arbitrary function satisfying the "theorem of the cube" identity: for all $x, y, z \in M$,
--   $$\Lambda(x+y+z) - \Lambda(x+y) - \Lambda(x+z) - \Lambda(y+z) + \Lambda(x) + \Lambda(y) + \Lambda(z) = \Lambda(0).$$
--   Then for all $x, y \in M$ and every integer $n$,
--   $$\Lambda(n \cdot x + y) = \Lambda(y) + n \cdot \bigl(\Lambda(x+y) - \Lambda(y)\bigr) + \frac{n(n-1)}{2} \cdot \bigl(\Lambda(2 \cdot x) - 2\Lambda(x) + \Lambda(0)\bigr),$$
--   where $n \cdot x$ and the scalar multiples on the right are the integer scalar multiplications of the groups $M$ and $N$, and the coefficient $n(n-1)/2$ is the integer quotient of $n(n-1)$ by $2$ in $\mathbb{Z}$ (exact, since $n(n-1)$ is even). No continuity, additivity or normalisation of $\Lambda$ beyond the displayed identity is assumed; in particular $\Lambda(0)$ need not vanish, and it occurs explicitly in the second difference.
--
--   This is the elementary group-theoretic core of the classical deduction, from the theorem of the cube, that pull-backs of a line bundle along $n$-fold multiples depend quadratically on $n$: with $M$ a group of maps into an abelian scheme, $N$ a Picard group and $\Lambda(\alpha) = [\alpha^{*}L]$, the cube identity becomes the stated functional equation. It is used in the treatment of the relative group law on Jacobians with good reduction, where the $n$-fold multiplication map is compared with tensor powers of a line bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_apply_zsmul_add_eq_of_forall_cube.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.apply_zsmul_add_eq_of_forall_cube
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) := by sorry
