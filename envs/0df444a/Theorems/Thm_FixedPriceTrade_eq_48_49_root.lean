-- Prove2me | Theorems.Thm_FixedPriceTrade_eq_48_49_root
-- name    : FixedPriceTrade.eq_48_49_root
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:33.436203+00:00
-- url     : https://prove2.me/theorems/25de7456-6037-4640-a5fd-88f601355162
-- title:
--   (48)–(49) — the root equation reads $S(C_*)=1+\tau(C_*)$ and $\beta_*=1/S(C_*)=1/(1+\tau(C_*))$
-- statement:
--   For $1/4<C<1/2$, the root equation (47),
--   $$
--   C(2+\mathcal I(C))=1+\frac{C^2}{1-2C}e^{-\mathcal I(C)/2}
--   $$
--   with $\mathcal I$ in its arctangent form, reads $S(C)=1+\tau(C)$. By (7)–(8), $S$ strictly decreases from infinity to one while $\tau$ strictly increases from zero to infinity, so this equation has exactly one root $C_*\in(1/4,1/2)$, and
--   $$
--   \beta_*=[C_*(2+\mathcal I(C_*))]^{-1}=\frac1{S(C_*)}=\frac1{1+\tau(C_*)} .
--   $$
--   This identifies the constant of Theorem A with the point of the scalar curve where $\beta_*\tau(C_*)=1-\beta_*$.
--
--   Differences from the source:
--   - encoding: (47) reads (48) → for each C ∈ (1/4, 1/2), (47) with the arctangent form holds if and only if S(C) = 1 + τ(C); reason: the two forms of the same equation
--   - reading: 'so (48) determines a unique C∗' (proof of Theorem A, p.23) → ∃! C ∈ (1/4, 1/2) with S(C) = 1 + τ(C); reason: the sentence that fixes C∗ is part of the milestone
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §10, (48)–(49), p.23

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade

open Set Real

/-- **The root equation (48)–(49)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.23.

On `1/4 < C < 1/2`, the root equation (47),
`C(2 + I(C)) = 1 + C²/(1 − 2C) e^{−I(C)/2}` with `I` in its arctangent form, reads
`S(C) = 1 + τ(C)` (48); it has exactly one root `C∗` in `(1/4, 1/2)` ("By (7)–(8), S strictly
decreases from infinity to one while τ strictly increases from zero to infinity, so (48)
determines a unique C∗", p.23); and at that root
`β∗ = [C∗(2 + I(C∗))]^{−1} = 1/S(C∗) = 1/(1 + τ(C∗))` (49). -/
theorem eq_48_49_root :
    (∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      (C * (2 + IArctan C) = 1 + C ^ 2 / (1 - 2 * C) * exp (-(IArctan C) / 2) ↔
        SCurve C = 1 + tauCurve C)) ∧
    (∃! C, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ SCurve C = 1 + tauCurve C) ∧
    ∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2), SCurve C = 1 + tauCurve C →
      (C * (2 + IArctan C))⁻¹ = 1 / SCurve C ∧ 1 / SCurve C = 1 / (1 + tauCurve C) := by sorry

end FixedPriceTrade
