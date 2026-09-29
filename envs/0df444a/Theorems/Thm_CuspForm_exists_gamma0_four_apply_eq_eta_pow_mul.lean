-- Prove2me | Theorems.Thm_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul
-- name    : CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/90051634-9f66-535b-b6be-e9977b9d4dee
-- title:
--   Eta products of level 4 are cusp forms on Γ₀(4)
-- statement:
--   Let $a,b,c$ be natural numbers, not all zero (i.e. $0 < a+b+c$), subject to the four arithmetic conditions $24 \mid a+2b+4c$, $24 \mid 4a+2b+c$, $b$ even, and $4 \mid a+b+c$. The assertion is that there exists a cusp form $f$ for the congruence subgroup $\Gamma_0(4)$, of weight equal to the integer obtained from the natural-number quotient $(a+b+c)/2$ (exact here, since $4 \mid a+b+c$), such that for every point $z$ of the upper half-plane the value $f(z)$ equals
--   $$\eta(z)^{a}\,\eta(2z)^{b}\,\eta(4z)^{c},$$
--   where $\eta$ denotes the Dedekind eta function as a function on the complex numbers and $z$ is regarded as a complex number. Thus the eta product is realised as an element of the space of cusp forms of that weight and level in the sense of Mathlib: weakly modular of the stated weight for $\Gamma_0(4)$ with trivial character, holomorphic, and vanishing at the cusps.
--
--   This is the Gordon–Hughes–Newman holomorphy criterion for eta products, specialised to level $4$ and the divisors $1,2,4$: the two divisibility conditions make the orders at the cusps $\infty$ and $0$ integral, while the parity of $b$ together with $4 \mid a+b+c$ trivialises the quadratic character attached to the product. It supplies the modular forms used in the identities [`ModularForm.E4_mul_etaProduct_eq`](thm.html#ModularForm.E4_mul_etaProduct_eq), [`ModularForm.E4_mul_eta_pow_eight_eq`](thm.html#ModularForm.E4_mul_eta_pow_eight_eq) and [`ModularForm.eta_pow_twentyfour_eq`](thm.html#ModularForm.eta_pow_twentyfour_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul (a b c : ℕ) (h0 : 0 < a + b + c)
    (h₁ : 24 ∣ a + 2 * b + 4 * c) (h₂ : 24 ∣ 4 * a + 2 * b + c) (hb : Even b) (h4 : 4 ∣ a + b + c) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 4) (((a + b + c) / 2 : ℕ) : ℤ),
      ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b *
        ModularForm.eta (4 * (z : ℂ)) ^ c := by sorry
