-- Prove2me | Theorems.Thm_FixedPriceTrade_sharpness
-- name    : FixedPriceTrade.sharpness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:27.327896+00:00
-- url     : https://prove2.me/theorems/376f31d1-7d3d-4743-88e3-3151a5394830
-- title:
--   Proof of Theorem A, sharpness — the hard family of (46) at $C_*$ has ratio $\to\beta_*$
-- statement:
--   Let $C_*\in(1/4,1/2)$ solve $S(C_*)=1+\tau(C_*)$, $d=\tau(C_*)$ and $\beta_*=1/S(C_*)$. Then:
--
--   1. for every $\eta\in(0,1]$, $H_{\eta,C_*}$ satisfies the hypotheses of Lemma 9.2 (continuous, nonincreasing, values in $[0,1]$, $H(1)=\eta$);
--   2. as $\eta\downarrow0$, $J_\eta=J_d(H_{\eta,C_*}(1-\cdot))\to S(C_*)=1/\beta_*$, and $T_\eta$ converges (to $T$ of $H_{C_*}$);
--   3. for $\eta\in(0,1)$ the hard pair is admissible, and its first-best welfare $M_\eta+G_\eta=\mathbb E\max$ is at least $d>0$;
--   4. the welfare ratio of the hard pair tends to $\beta_*$:
--   $$
--   \lim_{\eta\downarrow0}\frac{M_\eta+\Gamma_{\max,\eta}}{M_\eta+G_\eta}=\beta_* .
--   $$
--   Together with the guarantee this shows $r_{\mathrm{FP}}=\beta_*$.
--
--   Differences from the source:
--   - encoding: η ↓ 0 → Tendsto along 𝓝[>] 0, and an ε–δ limit of the ratio over every pair satisfying IsHardPair; reason: IsHardPair pins the pair, so this is the limit of the ratio of the family
--   - encoding: 'We use Lemma 9.2 with this survival function'; 'the denominator is at least the buyer mean, which is at least d' → the hypotheses of Lemma 9.2 for H_{η,C∗}, admissibility of the pair, and E max ≥ d; reason: the facts the page uses, stated as conclusions
--   - encoding: convergence of T_η → T_η → T of H_{C∗} = H_{0,C∗}; reason: names the limit
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), proof of Theorem A, Sharpness, p.23

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_J
import Definitions.Def_FixedPriceTrade_maxControl
import Definitions.Def_FixedPriceTrade_IsHardPair

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set Filter Topology

/-- **Sharpness (proof of Theorem A)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee
of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.23.

Let `C∗ ∈ (1/4, 1/2)` solve `S(C∗) = 1 + τ(C∗)`, `d = τ(C∗)`, `β∗ = 1/S(C∗)`. Then:

1. for every `η ∈ (0, 1]`, `H_{η,C∗}` of (46) satisfies the hypotheses of Lemma 9.2
   (continuous, nonincreasing, values in `[0,1]`, `H(1) = η`);
2. `J_η = J_d(H_{η,C∗}(1 − ·)) → S(C∗) = 1/β∗` and `T_η → T` of `H_{C∗}` as `η ↓ 0`;
3. for `η ∈ (0, 1)` the hard pair of (46) is admissible and its first-best welfare
   `M_η + G_η = E max` is at least `d`;
4. the welfare ratio of the hard pair tends to `β∗` as `η ↓ 0`.

**Formalization Note.** Item 4 is stated for every pair satisfying `IsHardPair`, which pins the
laws; it is the limit `lim_{η↓0} (M_η + Γ_max,η)/(M_η + G_η) = β∗`. -/
theorem sharpness (Cs : ℝ) (hCs : Cs ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : SCurve Cs = 1 + tauCurve Cs) :
    (∀ η ∈ Ioc (0 : ℝ) 1,
      ContinuousOn (Heta η Cs) (Icc 0 1) ∧ AntitoneOn (Heta η Cs) (Icc 0 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Heta η Cs s ∈ Icc (0 : ℝ) 1) ∧ Heta η Cs 1 = η) ∧
    Tendsto (fun η => J (tauCurve Cs) (fun t => Heta η Cs (1 - t))) (𝓝[>] 0)
      (𝓝 (SCurve Cs)) ∧
    Tendsto (fun η => hardT (tauCurve Cs) (Heta η Cs) 1) (𝓝[>] 0)
      (𝓝 (hardT (tauCurve Cs) (HC Cs) 1)) ∧
    (∀ η ∈ Ioo (0 : ℝ) 1, ∀ μs μb : Measure ℝ, IsHardPair (tauCurve Cs) (Heta η Cs) μs μb →
      IsAdmissiblePair μs μb ∧ tauCurve Cs ≤ expectedMax μs μb) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ η ∈ Ioo 0 δ, ∀ μs μb : Measure ℝ,
      IsHardPair (tauCurve Cs) (Heta η Cs) μs μb →
        |welfareRatio μs μb - 1 / SCurve Cs| < ε := by sorry

end FixedPriceTrade
