-- Prove2me | Theorems.Thm_Diaz_Exp0_add
-- name    : Diaz.Exp0_add
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:00.674718+00:00
-- url     : https://prove2.me/theorems/7fa254a7-a858-4b78-8cac-c955ac5db3fc
-- title:
--   The formal exponential is a homomorphism from the rational plane to $\mathbb{R}^{\times}$
-- statement:
--   For all pairs of rationals $x, y \in \mathbb{Q} \times \mathbb{Q}$, with addition taken componentwise,
--
--   $$\mathrm{Exp}_0(x + y)  =  \mathrm{Exp}_0(x)\,\mathrm{Exp}_0(y),$$
--
--   where $\mathrm{Exp}_0(a,b) = 2^{\,a+b}$.
--
--   **Why.** The coordinate sum $a+b$ is additive in the pair, and $2^{r+s} = 2^{r}2^{s}$ for real exponents.
--
--   **Role.** This is the first of the four properties the model's formal exponential must have. The rational plane spanned by a transcendental point $t$ of the circle and its conjugate is an additive group; the model requires a homomorphism from it into the multiplicative group of the algebraic numbers, commuting with the involution. Additivity is that homomorphism property, and it is what turns the kernel of $\mathrm{Exp}_0$ into a subgroup — the divisible line $a+b=0$, which is the first of the two "defects" the accompanying note turns on.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L78-L83

import Mathlib
import Definitions.Def_Diaz_Exponential

open ComplexConjugate
open Diaz

theorem Diaz.Exp0_add (x y : ℚ × ℚ) : Exp0 (x + y) = Exp0 x * Exp0 y := by sorry
