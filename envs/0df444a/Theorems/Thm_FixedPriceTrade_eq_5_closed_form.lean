-- Prove2me | Theorems.Thm_FixedPriceTrade_eq_5_closed_form
-- name    : FixedPriceTrade.eq_5_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:31.425636+00:00
-- url     : https://prove2.me/theorems/fae6fcaa-ed92-4034-879a-c68083ae6d78
-- title:
--   (5) — closed form of $\mathcal I(C)$ by arctangents
-- statement:
--   For $1/4<C<1/2$, with $\omega=\sqrt{C-1/4}$ and principal arctangents,
--   $$
--   \mathcal I(C)=\int_0^{y_e(C)}\frac{dr}{1-r+Cr^2}=\frac1\omega\Big(\arctan\frac{1-3C}{2(1-C)\omega}+\arctan\frac1{2\omega}\Big).
--   $$
--   This links the integral definition of the scalar curve to the closed form in which Theorem A states its root equation.
--
--   Differences from the source: none.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (5), p.10

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade

open Set

/-- **Closed form of `I(C)`** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), (5), p.10: for
`1/4 < C < 1/2`, with `ω = √(C − 1/4)` and principal arctangents,
`I(C) = (1/ω)(arctan((1 − 3C)/(2(1 − C)ω)) + arctan(1/(2ω)))`.

**Formalization Note.** `Real.arctan` is the principal arctangent. -/
theorem eq_5_closed_form : ∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2), Ical C = IArctan C := by sorry

end FixedPriceTrade
