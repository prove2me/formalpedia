-- Prove2me | Theorems.Thm_FiniteMagmaE677_magma496_generic
-- name    : FiniteMagmaE677.magma496_generic
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T00:12:03.703352+00:00
-- url     : https://prove2.me/theorems/db501e95-a0f2-40b0-a8c7-4aa0995b16c6
-- title:
--   The 496-element fibered construction satisfies E677 and is not right-cancellative (generic form)
-- statement:
--   Let $M$ be any commutative ring of characteristic two with $0 \neq 1$, containing elements $\zeta, \omega$ with $\zeta^4+\zeta^3+\zeta^2+\zeta+1 = 0$ (a primitive fifth root of unity) and $\omega^2+\omega+1 = 0$ (a primitive cube root of unity). Consider the operation on $\mathbb{Z}/31 \times M$ whose base coordinate is the affine operation $p \diamond_0 q = 3p - 2q$ and whose fiber coordinate is selected by the quadratic character of the difference $q_1 - p_1$ through Euler's criterion $d^{15}$: the diagonal uses $(1+\zeta)s + \zeta t$, square differences project to the second argument, and non-square differences use $(1+\omega)s + \omega t$.
--
--   Then this magma satisfies equation 677 and is not right-cancellative: the elements $(0,0)$ and $(0,1)$ have the same product with $(1,0)$, since the coordinate difference $1$ is a square and the square fiber projects onto the second argument.
--
--   This is the generic form of the blueprint's Chapter 13 construction of a finite non-right-cancellative model of equation 677; the four fiber selections inside the E677 identity carry the characters $-, -, +, +$ of $(y-x)^{15}$ because $2^{15} = 7^{15} = 1$ and $15^{15} = -1$ in $\mathbb{Z}/31$.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), section 'A finite non-right-cancellative example', https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here (generic characteristic-two form).

import Definitions.Def_FiniteMagmaE677
import Definitions.Def_FiniteMagmaE677_magma496

universe u v

theorem FiniteMagmaE677.magma496_generic {M : Type v} [CommRing M] (ζ ω : M)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hω : ω ^ 2 + ω + 1 = 0)
    (h2 : (1 : M) + 1 = 0) (h01 : (0 : M) ≠ 1) :
    FiniteMagmaE677.E677 (FiniteMagmaE677.magma496 ζ ω) ∧
    ∃ a b c : ZMod 31 × M,
      FiniteMagmaE677.magma496 ζ ω a c = FiniteMagmaE677.magma496 ζ ω b c ∧ a ≠ b := by sorry
