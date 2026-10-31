-- Prove2me | Theorems.Thm_ForkJoinDelay_sec_3_1_fj_cdf
-- name    : ForkJoinDelay.sec_3_1_fj_cdf
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:47.306893+00:00
-- url     : https://prove2.me/theorems/10aa34b7-e57d-40cb-85d4-ecf76f6a094b
-- title:
--   §3.1, p.12 — gamma sojourn laws and the fork-join CDF
-- statement:
--   Let $U_0,U_1,\dots$ and $G_0,G_1,\dots$ be the service times at UFJ and LFJ: measurable, mutually independent, exponential with rates $\mu_1,\mu_2>0$. A tagged customer arriving at UFJ (LFJ) and finding $x-1$ ($y-1$) customers there, $x,y\ge1$, has sojourn time $S_1=U_0+\cdots+U_{x-1}$ ($S_2=G_0+\cdots+G_{y-1}$). Then:
--
--   1. $S_1\sim\Gamma(x,\mu_1)$ and $S_2\sim\Gamma(y,\mu_2)$ (shape, rate);
--   2. for every $t\ge0$, $P(\max\{S_1,S_2\}\le t)=P(S_1\le t)\,P(S_2\le t)$;
--   3. $P(S_1\le t)=1-\sum_{m=0}^{x-1}e^{-\mu_1t}\frac{(\mu_1t)^m}{m!}$ and $P(S_2\le t)=1-\sum_{n=0}^{y-1}e^{-\mu_2t}\frac{(\mu_2t)^n}{n!}$;
--   4. hence
--   $$F_{S_{FJ}|x,y}(t)=P(\max\{S_1,S_2\}\le t)=\Bigl(1-\sum_{m=0}^{x-1}e^{-\mu_1t}\frac{(\mu_1t)^m}{m!}\Bigr)\Bigl(1-\sum_{n=0}^{y-1}e^{-\mu_2t}\frac{(\mu_2t)^n}{n!}\Bigr);$$
--   5. the same product is the distribution function of $\max(s,t)$ under $\Gamma(x,\mu_1)\otimes\Gamma(y,\mu_2)$, the law in the boundary transform $Z_{x,y}$.
--
--   This identifies the boundary transform $Z_{x,y}$ of (5) and gives the distribution function used to compute it.
--
--   Differences from the source:
--   - encoding: (S1|h1 = x), (S2|h2 = y): sojourn times given the station contents at the tagged customer's arrival → S1 = U0 + ⋯ + U(x−1), S2 = G0 + ⋯ + G(y−1) with independent exponential services; reason: the page's own description: 'the sum of x (y) service durations, each exponentially distributed'
--   - reading: service 'rates' µ1, µ2 → 0 < µ1, µ2; reason: a rate of an exponential law is positive
--   - reading: F_{SFJ|x,y}(t) for t (range not stated) → t ≥ 0; reason: the sojourn time is nonnegative; for t < 0 the distribution function is 0 and the printed formula is not meant there
--   - encoding: Gamma(x, µ1) → gammaMeasure (x : ℝ) µ1 (shape, rate); reason: Mathlib's parametrization is shape and rate, mean x/µ1, matching a sum of x Exp(µ1) terms
--   - encoding: probabilities P(·) → (P A).toReal for the ENNReal-valued measure; reason: P is a probability measure, so the value is finite; same number
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3.1, p.12 (paragraph after Eq. (5) and the display for F_{SFJ|x,y}(t))

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The fork-join sojourn law at the boundary: gamma laws and the CDF display of §3.1.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3.1, p.12: "The sojourn time of a tagged customer arriving at
the UFJ (LFJ) station and finding x − 1 (y − 1) customers there will be the sum of x (y) service
durations, each exponentially distributed with rate µ1 (µ2). Therefore, (S1|h1 = x) ∼
Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2)", and the display
`F_{S_FJ|x,y}(t) = P(S₁ ≤ t) P(S₂ ≤ t) = (1 − Σ_{m=0}^{x−1} e^{−µ₁t}(µ₁t)^m/m!)(1 − Σ_{n=0}^{y−1} e^{−µ₂t}(µ₂t)^n/n!)`.

Let `U 0, U 1, …` and `G 0, G 1, …` be service times at UFJ and LFJ: measurable, mutually
independent (one family), exponential with rates `µ₁, µ₂ > 0`. For `x, y ≥ 1` put
`S₁ = U 0 + ⋯ + U (x−1)` and `S₂ = G 0 + ⋯ + G (y−1)` (the tagged customer finds `x − 1`,
resp. `y − 1`, customers ahead). Then
1. `S₁ ∼ Gamma(x, µ₁)` and `S₂ ∼ Gamma(y, µ₂)` (shape, rate);
2. for every `t ≥ 0`, `P(max(S₁,S₂) ≤ t) = P(S₁ ≤ t) P(S₂ ≤ t)`;
3. `P(S₁ ≤ t) = 1 − Σ_{m<x} e^{−µ₁t}(µ₁t)^m/m!` and `P(S₂ ≤ t) = 1 − Σ_{n<y} e^{−µ₂t}(µ₂t)^n/n!`;
4. `P(max(S₁,S₂) ≤ t)` equals the product of the two brackets;
5. the same product is the CDF of `max` under `Gamma(x,µ₁) ⊗ Gamma(y,µ₂)`, the law against which
   `Z_{x,y}` (`boundaryLST`) integrates.

**Formalization Note.** The CDF formula is claimed for `t ≥ 0` (the sojourn time is
nonnegative; for `t < 0` both sides of the page's display are not meant). Mathlib's
`gammaMeasure a r` has shape `a` and rate `r`. -/
theorem sec_3_1_fj_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (U G : ℕ → Ω → ℝ)
    (hU : ∀ n, Measurable (U n)) (hG : ∀ n, Measurable (G n))
    (hind : iIndepFun (fun i : Fin 2 × ℕ => ![U, G] i.1 i.2) P)
    (hlawU : ∀ n, P.map (U n) = expMeasure μ₁) (hlawG : ∀ n, P.map (G n) = expMeasure μ₂)
    (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (t : ℝ) (ht : 0 ≤ t) :
    P.map (fun ω => ∑ i ∈ Finset.range x, U i ω) = gammaMeasure (x : ℝ) μ₁ ∧
    P.map (fun ω => ∑ i ∈ Finset.range y, G i ω) = gammaMeasure (y : ℝ) μ₂ ∧
    (P {ω | max (∑ i ∈ Finset.range x, U i ω) (∑ i ∈ Finset.range y, G i ω) ≤ t}).toReal =
      (P {ω | ∑ i ∈ Finset.range x, U i ω ≤ t}).toReal *
        (P {ω | ∑ i ∈ Finset.range y, G i ω ≤ t}).toReal ∧
    (P {ω | ∑ i ∈ Finset.range x, U i ω ≤ t}).toReal =
      1 - ∑ m ∈ Finset.range x, Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ m / (m.factorial : ℝ) ∧
    (P {ω | ∑ i ∈ Finset.range y, G i ω ≤ t}).toReal =
      1 - ∑ n ∈ Finset.range y, Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ n / (n.factorial : ℝ) ∧
    (P {ω | max (∑ i ∈ Finset.range x, U i ω) (∑ i ∈ Finset.range y, G i ω) ≤ t}).toReal =
      (1 - ∑ m ∈ Finset.range x, Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ m / (m.factorial : ℝ)) *
        (1 - ∑ n ∈ Finset.range y, Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ n / (n.factorial : ℝ)) ∧
    (((gammaMeasure (x : ℝ) μ₁).prod (gammaMeasure (y : ℝ) μ₂))
        {p : ℝ × ℝ | max p.1 p.2 ≤ t}).toReal =
      (1 - ∑ m ∈ Finset.range x, Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ m / (m.factorial : ℝ)) *
        (1 - ∑ n ∈ Finset.range y, Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ n / (n.factorial : ℝ)) := by sorry

end ForkJoinDelay
