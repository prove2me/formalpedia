-- Prove2me | Theorems.Thm_FixedPriceTrade_eq_7_8_scalar_curve
-- name    : FixedPriceTrade.eq_7_8_scalar_curve
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:25.915946+00:00
-- url     : https://prove2.me/theorems/91f7ecfd-1415-4fc4-9220-d594b76fda9d
-- title:
--   (7)–(8) — derivatives and limits of the scalar curve; the unique $C_d$
-- statement:
--   On $1/4<C<1/2$ one has $\mathcal I(C)>0$, $\tau(C)>0$ and
--   $$
--   \mathcal I'=-\frac{2(C\mathcal I+2)}{C(4C-1)},\qquad S'=\frac{(2C-1)\mathcal I+8C-6}{4C-1}<0,\qquad \frac{\tau'}{\tau}=\frac{S'}{2C-1}>0 .
--   $$
--   At the endpoints
--   $$
--   (S(C),\tau(C))\to(\infty,0)\ (C\downarrow1/4),\qquad (S(C),\tau(C))\to(1,\infty)\ (C\uparrow1/2).
--   $$
--   In particular, for every $d>0$ there is a unique $C_d\in(1/4,1/2)$ with $\tau(C_d)=d$.
--
--   This monotonicity is what selects one curvature parameter for each initial state, and gives the uniqueness of the root $C_*$.
--
--   Differences from the source:
--   - encoding: τ′/τ = S′/(2C − 1) > 0 → τ > 0, τ′ = τ·S′/(2C − 1), and S′/(2C − 1) > 0; reason: the same statement without dividing by τ
--   - encoding: limits as C ↓ 1/4 and C ↑ 1/2 → Tendsto along 𝓝[>] (1/4) and 𝓝[<] (1/2); reason: Mathlib's one-sided limits
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (7)–(8), p.11

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade

open Set Filter Topology

/-- **Derivatives, limits and `C_d`** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee
of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), (7)–(8), p.11.

On `1/4 < C < 1/2`: `I > 0`;
`I′ = −2(CI + 2)/(C(4C − 1))`; `S′ = ((2C − 1)I + 8C − 6)/(4C − 1) < 0`; `τ > 0` and
`τ′/τ = S′/(2C − 1) > 0`. At the endpoints `(S, τ) → (∞, 0)` as `C ↓ 1/4` and `(S, τ) → (1, ∞)`
as `C ↑ 1/2`. For every `d > 0` there is a unique `C_d ∈ (1/4, 1/2)` with `τ(C_d) = d`.

**Formalization Note.** `τ′/τ = S′/(2C − 1)` is stated as `τ′ = τ · S′/(2C − 1)`, with `τ > 0`.
The one-sided limits are along `𝓝[>] (1/4)` and `𝓝[<] (1/2)`. -/
theorem eq_7_8_scalar_curve :
    (∀ C ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      0 < Ical C ∧
      HasDerivAt Ical (-2 * (C * Ical C + 2) / (C * (4 * C - 1))) C ∧
      HasDerivAt SCurve (((2 * C - 1) * Ical C + 8 * C - 6) / (4 * C - 1)) C ∧
      ((2 * C - 1) * Ical C + 8 * C - 6) / (4 * C - 1) < 0 ∧
      0 < tauCurve C ∧
      HasDerivAt tauCurve
        (tauCurve C * ((((2 * C - 1) * Ical C + 8 * C - 6) / (4 * C - 1)) / (2 * C - 1))) C ∧
      0 < (((2 * C - 1) * Ical C + 8 * C - 6) / (4 * C - 1)) / (2 * C - 1)) ∧
    Tendsto SCurve (𝓝[>] (1 / 4)) atTop ∧
    Tendsto tauCurve (𝓝[>] (1 / 4)) (𝓝 0) ∧
    Tendsto SCurve (𝓝[<] (1 / 2)) (𝓝 1) ∧
    Tendsto tauCurve (𝓝[<] (1 / 2)) atTop ∧
    ∀ d : ℝ, 0 < d → ∃! C, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ tauCurve C = d := by sorry

end FixedPriceTrade
