-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_9_1
-- name    : FixedPriceTrade.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:23.770472+00:00
-- url     : https://prove2.me/theorems/94bfe9dd-8d6c-476f-8b41-22467698e977
-- title:
--   Lemma 9.1 — pricing from the variational bound, $\Gamma(z)\ge\beta G-\beta d\,M$
-- statement:
--   Let $0<\beta<1$ and $d>0$. If
--   $$
--   \beta\sup_{0\le h\le1}J_d(h)\le1,
--   $$
--   then every independent pair of nonnegative finite-mean distributions admits a price $z\ge0$ with
--   $$
--   \Gamma(z)\ge\beta G-\beta d\cdot M .
--   $$
--   This converts the variational bound of Theorem C into a fixed-price guarantee; at $d=\tau(C_*)$, $\beta=\beta_*$ it gives $M+\Gamma_{\max}\ge\beta_*(M+G)$.
--
--   Differences from the source:
--   - encoding: independent values V_s, V_b → the joint law is the product μs.prod μb of the two laws; reason: for independent variables the joint law is the product, and every quantity used depends only on the joint law
--   - encoding: β sup_{0≤h≤1} J_d(h) ≤ 1 → β·J_d(h) ≤ 1 for every control h; reason: equivalent since β > 0 (J_d is bounded above), and avoids a supremum junk value
--   - encoding: independent pair of finite-mean distributions (nonnegative by §3) → probability laws on ℝ with μ(Iio 0) = 0 and integrable identity; E max > 0 not assumed; reason: the page treats E V_b = 0 and assumes only finite means
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 9.1, p.20

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_J

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 9.1 (pricing from the variational bound)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
p.20.

Let `0 < β < 1` and `d > 0`. If `β sup_{0 ≤ h ≤ 1} J_d(h) ≤ 1` (38), then every independent pair of
nonnegative finite-mean distributions admits a price `z ≥ 0` with `Γ(z) ≥ βG − βd·M` (39).

**Formalization Note.** (38) is stated as `β J_d(h) ≤ 1` for every control `h`, which is the same
condition since `β > 0` and avoids a supremum junk value. The pair is any two probability laws on
`ℝ`, a.s. nonnegative (§3) with finite means; `E max > 0` is not assumed, as on the page.
Independence is the product law. -/
theorem lemma_9_1 (β d : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 0 < d)
    (h38 : ∀ h : ℝ → ℝ, IsControl h → β * J d h ≤ 1)
    (μs μb : Measure ℝ) [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]
    (hs0 : μs (Iio 0) = 0) (hb0 : μb (Iio 0) = 0)
    (hsi : Integrable (fun s : ℝ => s) μs) (hbi : Integrable (fun b : ℝ => b) μb) :
    ∃ z, 0 ≤ z ∧ β * firstBestGFT μs μb - β * d * sellerMean μs ≤ priceGFT μs μb z := by sorry

end FixedPriceTrade
