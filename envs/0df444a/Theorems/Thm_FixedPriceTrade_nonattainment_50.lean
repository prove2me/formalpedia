-- Prove2me | Theorems.Thm_FixedPriceTrade_nonattainment_50
-- name    : FixedPriceTrade.nonattainment_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:02.401298+00:00
-- url     : https://prove2.me/theorems/b5a1f164-6d15-4391-9460-61df1faf2f8b
-- title:
--   Proof of Theorem A, nonattainment (50) — the price density has mass $\alpha<1$
-- statement:
--   Let $C_*\in(1/4,1/2)$ solve $S(C_*)=1+\tau(C_*)$, $d=\tau(C_*)$ and $\beta_*=1/S(C_*)$. Let $(V_s,V_b)$ be admissible with $G>0$. In the cutoff normalization of Lemma 9.1 (values divided by the unique $s_0>0$ with $d\,s_0=\mathbb E(V_b-s_0)_+$, so that $L(1)=d$), let $H(u)=\Pr(V_b>s_0u)$. Then the density (40) has mass
--   $$
--   \alpha=\beta_*J_d(H(1-\cdot))<1,\qquad \alpha\,\Gamma_{\max}\ge\beta_*G-(1-\beta_*)M,
--   $$
--   $\Gamma_{\max}>0$, and
--   $$
--   M+\Gamma_{\max}-\beta_*(M+G)\ge(1-\alpha)\Gamma_{\max}>0 .
--   $$
--   If $G=0$, the welfare ratio is one. Hence every pair has ratio strictly above $\beta_*$.
--
--   Differences from the source:
--   - encoding: independent values V_s, V_b → the joint law is the product μs.prod μb of the two laws; reason: for independent variables the joint law is the product, and every quantity used depends only on the joint law
--   - encoding: nonnegative values with 0 < E max{V_s, V_b} < ∞ → probability laws on ℝ with μ(Iio 0) = 0, max integrable on the product, and 0 < ∫ max; reason: almost-sure nonnegativity and integrability are the measure-theoretic form of the printed hypothesis; atoms and unbounded supports remain allowed
--   - encoding: the cutoff normalization of Lemma 9.1 and (50) in normalized values → the cutoff s₀ stated on the original values (∃! s₀ > 0 with d s₀ = E(V_b − s₀)₊), H(u) = Pr(V_b > s₀u), and (50) with M, G, Γ_max of the original values; reason: M, G and Γ_max are homogeneous of degree one, so (50) is the same inequality in either scale
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), proof of Theorem A, Nonattainment, (50), p.23

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_SCurve
import Definitions.Def_FixedPriceTrade_J

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Nonattainment, (50) (proof of Theorem A)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.23.

Let `C∗ ∈ (1/4, 1/2)` solve `S(C∗) = 1 + τ(C∗)`, `d = τ(C∗)` and `β∗ = 1/S(C∗)`. For every admissible
pair with `G > 0`:

1. the cutoff `s₀ > 0` of Lemma 9.1, the zero of `d·s − E(V_b − s)₊`, exists and is unique; in the
   normalized values `V/s₀` the buyer tail integral has `L(1) = d` and survival function
   `H(u) = Pr(V_b > s₀ u)`;
2. the mass `α = β∗ J_d(H(1 − ·))` of the price density (40) satisfies `0 ≤ α < 1` and
   `α Γ_max ≥ β∗ G − (1 − β∗) M` (50);
3. `Γ_max > 0`, and `M + Γ_max − β∗(M + G) ≥ (1 − α) Γ_max`.

If `G = 0`, the welfare ratio is one.

**Formalization Note.** `Γ_max`, `G`, `M` are those of the original values: all three are
homogeneous of degree one, so (50) in the normalized values is the same inequality. -/
theorem nonattainment_50 (Cs : ℝ) (hCs : Cs ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : SCurve Cs = 1 + tauCurve Cs) (μs μb : Measure ℝ) (hp : IsAdmissiblePair μs μb) :
    (0 < firstBestGFT μs μb →
      (∃! s₀ : ℝ, 0 < s₀ ∧ tauCurve Cs * s₀ = ∫ b, max (b - s₀) 0 ∂μb) ∧
      ∀ s₀ : ℝ, 0 < s₀ → tauCurve Cs * s₀ = ∫ b, max (b - s₀) 0 ∂μb →
        0 ≤ 1 / SCurve Cs * J (tauCurve Cs) (fun t => (μb (Ioi (s₀ * (1 - t)))).toReal) ∧
        1 / SCurve Cs * J (tauCurve Cs) (fun t => (μb (Ioi (s₀ * (1 - t)))).toReal) < 1 ∧
        1 / SCurve Cs * firstBestGFT μs μb - (1 - 1 / SCurve Cs) * sellerMean μs ≤
          1 / SCurve Cs * J (tauCurve Cs) (fun t => (μb (Ioi (s₀ * (1 - t)))).toReal) *
            gammaMax μs μb ∧
        0 < gammaMax μs μb ∧
        (1 - 1 / SCurve Cs * J (tauCurve Cs) (fun t => (μb (Ioi (s₀ * (1 - t)))).toReal)) *
            gammaMax μs μb ≤
          sellerMean μs + gammaMax μs μb -
            1 / SCurve Cs * (sellerMean μs + firstBestGFT μs μb)) ∧
    (firstBestGFT μs μb = 0 → welfareRatio μs μb = 1) := by sorry

end FixedPriceTrade
