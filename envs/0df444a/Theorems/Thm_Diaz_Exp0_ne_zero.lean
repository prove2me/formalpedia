-- Prove2me | Theorems.Thm_Diaz_Exp0_ne_zero
-- name    : Diaz.Exp0_ne_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:03.646879+00:00
-- url     : https://prove2.me/theorems/36ffbbf7-e7c3-42c5-84b1-0cf6b40faa1f
-- title:
--   The formal exponential never vanishes
-- statement:
--   For every pair of rationals $x = (a,b)$,
--
--   $$\mathrm{Exp}_0(a,b)  =  2^{\,a+b}  \neq  0 .$$
--
--   **Why.** $2^{r} > 0$ for every real $r$, the real power of a positive base being positive.
--
--   **Role.** A homomorphism into a multiplicative group has to land in the units, and this is that check for $\mathrm{Exp}_0$ as a map from the additive rational plane to $\mathbb{R}^{\times}$. It is what makes the companion statements $\mathrm{Exp}_0(x+y) = \mathrm{Exp}_0(x)\,\mathrm{Exp}_0(y)$ and $\mathrm{Exp}_0(x)^{n} = 1 \Leftrightarrow \mathrm{Exp}_0(x) = 1$ statements about a group rather than a monoid.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L76-L76

import Mathlib
import Definitions.Def_Diaz_Exponential

open ComplexConjugate
open Diaz

theorem Diaz.Exp0_ne_zero (x : ℚ × ℚ) : Exp0 x ≠ 0 := by sorry
