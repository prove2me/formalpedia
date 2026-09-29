-- Prove2me | Theorems.Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint
-- name    : AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/82789355-64c8-5f35-9132-3bf368abb7c3
-- title:
--   Adjoint endomorphisms under a perfect pairing have equinumerous kernels
-- statement:
--   Let $P$ be a finite additive abelian group and $K$ a field, and let $e : P \times P \to K^{\times}$ be a map into the units of $K$ which is bimultiplicative in the sense that $e(x + x', y) = e(x,y)\,e(x',y)$ and $e(x, y + y') = e(x,y)\,e(x,y')$ for all $x, x', y, y' \in P$. Assume $e$ is non-degenerate on both sides: if $e(x,y) = 1$ for all $y$ then $x = 0$, and if $e(x,y) = 1$ for all $x$ then $y = 0$. Assume furthermore that every character of $P$ is represented on the right by $e$, that is, for every group homomorphism $\chi$ from the multiplicative group `Multiplicative P` to $K^{\times}$ there exists $y \in P$ with $e(x,y) = \chi(x)$ for all $x \in P$ (the element $x$ being transported along `Multiplicative.ofAdd`). Let $T, T' : P \to P$ be additive endomorphisms which are adjoint for $e$, i.e. $e(Tx, y) = e(x, T'y)$ for all $x, y \in P$. Then the kernels of $T$ and of $T'$ have the same cardinality, $\#\ker T = \#\ker T'$ as natural numbers.
--
--   This is the standard orthogonal-complement count for a perfect pairing of a finite abelian group into the units of a field: the kernel of $T'$ is the right annihilator of the image of $T$, whose order is $\#P/\#\operatorname{im} T = \#\ker T$. It is applied to the $n$-torsion of a Jacobian with the Weil pairing, for which $1 - F_*^N$ and $1 - (F^*)^N$ are adjoint, in the finiteness statement [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
    {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y) (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0) (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card (T.ker) = Nat.card (T'.ker) := by sorry
