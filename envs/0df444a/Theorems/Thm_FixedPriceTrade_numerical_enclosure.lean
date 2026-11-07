-- Prove2me | Theorems.Thm_FixedPriceTrade_numerical_enclosure
-- name    : FixedPriceTrade.numerical_enclosure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:47.635004+00:00
-- url     : https://prove2.me/theorems/623bed86-a809-49a3-9659-3ca3b737e42c
-- title:
--   Numerical values — $0.73802433573<\beta_*<0.73802433574$, $C_*\approx0.3937571625$, $7/20<\tau(C_*)<9/25$
-- statement:
--   Let $C_*\in(1/4,1/2)$ be the root of $S(C)=1+\tau(C)$ and $\beta_*=1/S(C_*)$. Then
--   $$
--   0.73802433573<\beta_*<0.73802433574,\qquad 0.39375716245<C_*<0.39375716255,\qquad \frac7{20}<\tau(C_*)<\frac9{25} .
--   $$
--   The paper obtains these by interval arithmetic from (3)–(5) and (48).
--
--   Differences from the source:
--   - reading: C∗ ≈ 0.3937571625 → 0.39375716245 < C∗ < 0.39375716255; reason: ten printed digits read as correct rounding; the computed value is 0.39375716251478…
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §10, Numerical values, p.23

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade

open Set

/-- **Numerical values** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of Fixed-Price
Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.23: "Interval arithmetic gives
0.73802433573 < β∗ < 0.73802433574 from (3)–(5) and the root equation (48). The corresponding
parameter is C∗ ≈ 0.3937571625, with 7/20 < τ(C∗) < 9/25."

For the root `C∗ ∈ (1/4, 1/2)` of `S(C) = 1 + τ(C)` and `β∗ = 1/S(C∗)`:
`0.73802433573 < β∗ < 0.73802433574` and `7/20 < τ(C∗) < 9/25`.

and `C∗ ≈ 0.3937571625`, read as the ten-digit rounding: `0.39375716245 < C∗ < 0.39375716255`.

**Formalization Note.** "≈" with ten printed digits is read as correct rounding to those digits. -/
theorem numerical_enclosure (Cs : ℝ) (hCs : Cs ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : SCurve Cs = 1 + tauCurve Cs) :
    (73802433573 : ℝ) / 10 ^ 11 < 1 / SCurve Cs ∧ 1 / SCurve Cs < (73802433574 : ℝ) / 10 ^ 11 ∧
    (39375716245 : ℝ) / 10 ^ 11 < Cs ∧ Cs < (39375716255 : ℝ) / 10 ^ 11 ∧
    (7 : ℝ) / 20 < tauCurve Cs ∧ tauCurve Cs < (9 : ℝ) / 25 := by sorry

end FixedPriceTrade
