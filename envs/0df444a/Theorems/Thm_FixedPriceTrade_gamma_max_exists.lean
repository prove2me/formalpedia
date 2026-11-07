-- Prove2me | Theorems.Thm_FixedPriceTrade_gamma_max_exists
-- name    : FixedPriceTrade.gamma_max_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:30.80424+00:00
-- url     : https://prove2.me/theorems/211aea73-c306-4b86-9059-e88fb67b361f
-- title:
--   §3 — the maximum of $\Gamma$ over prices $z\ge0$ exists
-- statement:
--   Let $(V_s,V_b)$ be an admissible pair. Then $\Gamma$ is upper semicontinuous on $[0,\infty)$, and for every $z\ge0$
--   $$
--   \Gamma(z)\le\mathbb E\big[V_b\mathbf 1\{V_b\ge z\}\big]\xrightarrow[z\to\infty]{}0 .
--   $$
--   Consequently some $z\ge0$ maximizes $\Gamma$ over $[0,\infty)$, and $\Gamma_{\max}$ is that maximum. If $\Gamma$ is identically zero on $[0,\infty)$, every price is optimal.
--
--   This is what makes $\Gamma_{\max}=\max_{z\ge0}\Gamma(z)$ in the welfare ratio well defined; it relies on the inclusive convention $V_s\le z\le V_b$.
--
--   Differences from the source:
--   - encoding: independent values V_s, V_b → the joint law is the product μs.prod μb of the two laws; reason: for independent variables the joint law is the product, and every quantity used depends only on the joint law
--   - encoding: nonnegative values with 0 < E max{V_s, V_b} < ∞ → probability laws on ℝ with μ(Iio 0) = 0, max integrable on the product, and 0 < ∫ max; reason: almost-sure nonnegativity and integrability are the measure-theoretic form of the printed hypothesis; atoms and unbounded supports remain allowed
--   - encoding: Γ_max = max_{z≥0} Γ(z) → a maximizer z ≥ 0 exists and the supremum gammaMax equals Γ(z); reason: the supremum is the definition used throughout; this clause connects it to the maximum
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, p.10

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set Filter Topology

/-- **Existence of the maximum** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §3, p.10: "The maximum
exists: the inclusive rule makes Γ upper semicontinuous by reverse Fatou, and
Γ(z) ≤ E[V_b 1{V_b ≥ z}] → 0 as z → ∞. If Γ is identically zero, every price is optimal."

For an admissible pair: `Γ` is upper semicontinuous on `[0, ∞)`; `Γ(z) ≤ E[V_b 1{V_b ≥ z}]` for
`z ≥ 0`; that bound tends to `0`; some `z ≥ 0` maximizes `Γ` over `[0, ∞)`, and the supremum
`gammaMax` equals that maximum; if `Γ ≡ 0` on `[0, ∞)` every `z ≥ 0` is a maximizer.

**Formalization Note.** Independence is the product law (see `IsAdmissiblePair`). -/
theorem gamma_max_exists (μs μb : Measure ℝ) (hp : IsAdmissiblePair μs μb) :
    UpperSemicontinuousOn (priceGFT μs μb) (Ici 0) ∧
    (∀ z, 0 ≤ z → priceGFT μs μb z ≤ ∫ b, (Ici z).indicator (fun b => b) b ∂μb) ∧
    Tendsto (fun z => ∫ b, (Ici z).indicator (fun b => b) b ∂μb) atTop (𝓝 0) ∧
    (∃ z, 0 ≤ z ∧ (∀ z', 0 ≤ z' → priceGFT μs μb z' ≤ priceGFT μs μb z) ∧
      gammaMax μs μb = priceGFT μs μb z) ∧
    ((∀ z, 0 ≤ z → priceGFT μs μb z = 0) →
      ∀ z, 0 ≤ z → ∀ z', 0 ≤ z' → priceGFT μs μb z' ≤ priceGFT μs μb z) := by sorry

end FixedPriceTrade
