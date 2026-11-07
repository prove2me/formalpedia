-- Prove2me | Theorems.Thm_FixedPriceTrade_theorem_A
-- name    : FixedPriceTrade.theorem_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:33.017934+00:00
-- url     : https://prove2.me/theorems/13234b34-a90e-421c-aaed-fa9aaf798b00
-- title:
--   Theorem A — the exact welfare guarantee of fixed-price bilateral trade is $\beta_*\approx0.73802$
-- statement:
--   Let $V_s,V_b$ be independent nonnegative values with $0<\mathbb E\max\{V_s,V_b\}<\infty$, and let a fixed price $z\ge0$ trade when $V_s\le z\le V_b$. Let $C_*$ be the unique root in $(1/4,1/2)$ of
--   $$
--   C(2+\mathcal I(C))=1+\frac{C^2}{1-2C}e^{-\mathcal I(C)/2},\qquad \mathcal I(C)=\frac1{\sqrt{C-1/4}}\Big[\arctan\frac{1-3C}{2(1-C)\sqrt{C-1/4}}+\arctan\frac1{2\sqrt{C-1/4}}\Big],
--   $$
--   and $\beta_*=[C_*(2+\mathcal I(C_*))]^{-1}$. Then the optimal universal welfare guarantee of a fixed price is
--   $$
--   \inf_{F_s,F_b}\ \max_{z\ge0}\ \frac{\mathbb EV_s+\mathbb E\big[(V_b-V_s)\mathbf 1\{V_s\le z\le V_b\}\big]}{\mathbb E\max\{V_s,V_b\}}=\beta_*,\qquad 0.73802433573<\beta_*<0.73802433574 .
--   $$
--   More precisely:
--
--   1. the root $C_*$ exists and is unique;
--   2. for every pair the maximum over $z\ge0$ is attained;
--   3. every pair has ratio strictly greater than $\beta_*$;
--   4. $\beta_*$ is the greatest lower bound of the ratios;
--   5. for every $\varepsilon>0$ the explicit bounded family of Lemma 9.2 with survival functions $H_{\eta,C_*}$ of (46), $d=\tau(C_*)$, contains an admissible pair with ratio below $\beta_*+\varepsilon$.
--
--   So a single posted price always keeps more than $73.8\%$ of first-best welfare, and no larger fraction can be guaranteed.
--
--   Differences from the source:
--   - encoding: independent values V_s, V_b → the joint law is the product μs.prod μb of the two laws; reason: for independent variables the joint law is the product, and every quantity used depends only on the joint law
--   - encoding: nonnegative values with 0 < E max{V_s, V_b} < ∞ → probability laws on ℝ with μ(Iio 0) = 0, max integrable on the product, and 0 < ∫ max; reason: almost-sure nonnegativity and integrability are the measure-theoretic form of the printed hypothesis; atoms and unbounded supports remain allowed
--   - encoding: inf_{F_s,F_b} → IsGLB of the set of ratios of admissible pairs; reason: avoids an infimum junk value; the set is nonempty
--   - encoding: max_{z≥0} in the ratio → a clause that the maximum is attained, and the ratio built from the supremum over z ≥ 0; reason: the supremum equals the attained maximum
--   - reading: β∗ ≈ 0.73802 → 0.73802433573 < β∗ < 0.73802433574; reason: the enclosure printed on p.23 for the same constant; it implies the five-digit value
--   - encoding: the explicit bounded family in Lemma 9.2 → pairs satisfying IsHardPair (τ(C∗), H_{η,C∗}) with η ∈ (0,1), stated admissible; reason: (46), p.22: 'We use Lemma 9.2 with this survival function'; the predicate pins the pair
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Theorem A, p.22; Numerical values, p.23

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_SCurve
import Definitions.Def_FixedPriceTrade_maxControl
import Definitions.Def_FixedPriceTrade_IsHardPair

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set Real

/-- **Theorem A (exact welfare guarantee)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.22
(numerical values p.23).

Let `V_s, V_b` be independent nonnegative values with `0 < E max{V_s, V_b} < ∞`, and let a fixed
price `z ≥ 0` trade when `V_s ≤ z ≤ V_b`. Then:

(a) the root equation (47), `C(2 + I(C)) = 1 + C²/(1 − 2C) e^{−I(C)/2}` with
    `I(C) = (C − 1/4)^{−1/2}[arctan((1 − 3C)/(2(1 − C)√(C − 1/4))) + arctan(1/(2√(C − 1/4)))]`,
    has a unique root `C∗` in `(1/4, 1/2)`; put `β∗ = [C∗(2 + I(C∗))]^{−1}`;
(b) for every pair the maximum over `z ≥ 0` of `Γ(z)` is attained;
(c) every pair has welfare ratio `max_z (E V_s + Γ(z)) / E max{V_s, V_b}` strictly greater than
    `β∗`;
(d) `β∗` is the greatest lower bound of the ratios (`inf_{F_s, F_b} … = β∗`);
(e) for every `ε > 0` the explicit bounded family of Lemma 9.2 with the survival functions (46) at
    `C = C∗`, `d = τ(C∗)` contains an (admissible) pair with ratio below `β∗ + ε`;
(f) `0.73802433573 < β∗ < 0.73802433574` (the "≈ 0.73802" of the page, as enclosed on p.23).

**Formalization Note.** Independence is the product law; nonnegativity is almost sure;
`0 < E max < ∞` is integrability and positivity of `∫ max` (`IsAdmissiblePair`). Atoms and
unbounded supports are allowed. The infimum is stated as `IsGLB` of the set of ratios. The family
member is pinned by `IsHardPair`. -/
theorem theorem_A :
    (∃! C, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧
      C * (2 + IArctan C) = 1 + C ^ 2 / (1 - 2 * C) * exp (-(IArctan C) / 2)) ∧
    ∀ Cs : ℝ, Cs ∈ Ioo (1 / 4 : ℝ) (1 / 2) →
      Cs * (2 + IArctan Cs) = 1 + Cs ^ 2 / (1 - 2 * Cs) * exp (-(IArctan Cs) / 2) →
      (∀ μs μb : Measure ℝ, IsAdmissiblePair μs μb →
        (∃ z, 0 ≤ z ∧ ∀ z', 0 ≤ z' → priceGFT μs μb z' ≤ priceGFT μs μb z) ∧
        (Cs * (2 + IArctan Cs))⁻¹ < welfareRatio μs μb) ∧
      IsGLB {r | ∃ μs μb : Measure ℝ, IsAdmissiblePair μs μb ∧ welfareRatio μs μb = r}
        (Cs * (2 + IArctan Cs))⁻¹ ∧
      (∀ ε > 0, ∃ η ∈ Ioo (0 : ℝ) 1, ∃ μs μb : Measure ℝ,
        IsHardPair (tauCurve Cs) (Heta η Cs) μs μb ∧ IsAdmissiblePair μs μb ∧
        welfareRatio μs μb < (Cs * (2 + IArctan Cs))⁻¹ + ε) ∧
      (73802433573 : ℝ) / 10 ^ 11 < (Cs * (2 + IArctan Cs))⁻¹ ∧
      (Cs * (2 + IArctan Cs))⁻¹ < (73802433574 : ℝ) / 10 ^ 11 := by sorry

end FixedPriceTrade
