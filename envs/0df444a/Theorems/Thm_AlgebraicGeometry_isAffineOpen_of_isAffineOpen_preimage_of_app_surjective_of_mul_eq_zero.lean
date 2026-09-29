-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
-- name    : AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d3ca2828-9efd-5504-9c4a-fdf760b697f8
-- title:
--   Affineness descends along a surjective square-zero thickening
-- statement:
--   Let $X$ and $X'$ be schemes (in a fixed universe) and let $i : X \to X'$ be a morphism of schemes which is surjective, i.e. surjective on underlying points. Assume the hypothesis `hsq`: for every open $V \subseteq X'$ which is an affine open and all sections $a, b \in \Gamma(X', V)$, if the ring homomorphism $\Gamma(X', V) \to \Gamma(X, i^{-1}V)$ induced by $i$ on $V$ annihilates both $a$ and $b$, then $ab = 0$ in $\Gamma(X', V)$ — thus the kernel of $i^{\ast}$ has square zero on affine opens. Let $U \subseteq X'$ be an open subset such that the preimage open $i^{-1}U \subseteq X$ is an affine open, and such that the induced ring homomorphism $\Gamma(X', U) \to \Gamma(X, i^{-1}U)$ is surjective as a map of sets. The conclusion is that $U$ is itself an affine open of $X'$.
--
--   This is the non-cohomological half of the classical statement that a first-order (square-zero) thickening of an affine scheme is affine (EGA I 5.1.9), the lifting of sections being imposed here as a hypothesis rather than deduced. It is used in the proof that an open whose preimage under a flat pullback square is affine is itself affine, via [`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat`](thm.html#AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
    {X X' : Scheme.{u}} (i : X ⟶ X') [Surjective i]
    (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : Γ(X', V), (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
    (U : X'.Opens) (hU : IsAffineOpen (i ⁻¹ᵁ U)) (hsurj : Function.Surjective (i.app U).hom) : IsAffineOpen U := by sorry
