-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_theorem_4_1
-- name    : CalibratedMA.Randomized.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:59.992285+00:00
-- url     : https://prove2.me/theorems/0acc6ed4-1aa6-47f4-9c62-3bd5c50061ad
-- title:
--   Theorem 4.1 — randomized upper bound for calibrated multiaccuracy
-- statement:
--   There is a universal constant $C<\infty$ such that the following holds. Let $\mathcal X$ be a measurable space and $\mathcal G$ a finite class of measurable functions $g:\mathcal X\to[-1,1]$. Let $(X_1,Y_1),\dots,(X_n,Y_n)$ be $n\ge2$ i.i.d. samples from a distribution $\mathcal D$ on $\mathcal X\times[0,1]$, and let $\delta\in(0,1/2)$. Then, with probability at least $1-\delta$ over the training sample, Algorithm 1 returns a randomized predictor $Q=(Q_x)_{x\in\mathcal X}$ such that
--   $$\mathrm{CMA}(Q;\mathcal G)\le C\left\{\sqrt{\frac{\log(2|\mathcal G|/\delta)}{n}}+\Big(\frac{\log(2n/\delta)}{n}\Big)^{2/5}\right\}.$$
--
--   This is the randomized upper bound of the paper: $O(\log|\mathcal G|/\varepsilon^2+\varepsilon^{-5/2})$ samples (up to logarithmic factors) suffice for calibrated multiaccuracy error $\varepsilon$ with a randomized predictor. The bound concerns the specific output of Algorithm 1: its online learner, its parameters $m,\rho,M_*$, its greedy partition and its uniform mixture of rounded rules.
--
--   **Formalization Note.** The constant is quantified first (`∃ C > 0`), before the input space, the distribution, $\mathcal G$, $n$ and $\delta$. The sample is `ω : Fin n → X × ℝ` under the product measure $\mathcal D^{\otimes n}$. The conclusion bounds the outer measure of the failure set by $\delta$, which needs no measurability of that set. The good event also requires the output to be a measurable randomized predictor, so the joint law used in $\mathrm{CMA}$ is the true one. $|\mathcal G|$ is the cardinality of the `Finset`; for $\mathcal G=\emptyset$, Lean's $\log 0=0$ leaves only the second term, and $\mathrm{MA}=0$.
--
--   Differences from the source:
--   - encoding: distribution on $\mathcal X\times[0,1]$ → probability measure on $\mathcal X\times\mathbb R$ with $Y\in[0,1]$ almost surely; reason: same instances.
--   - encoding: $g:\mathcal X\to[-1,1]$ → measurable $g$; reason: $\mathbb E[g(X)(Y-P)]$ is undefined otherwise; measurability only excludes undefined cases.
--   - encoding: "with probability at least $1-\delta$ over the training sample and the construction randomness" → the $\mathcal D^{\otimes n}$-outer measure of the set of samples on which the conclusion fails is at most $\delta$; reason: Algorithm 1's training is deterministic given the sample, and the output's internal randomness (the index $J$ and the rounding) is part of $Q$; bounding the bad set is the strong reading.
--   - encoding: "Algorithm 1 returns a randomized predictor" → `IsRandomizedPredictor` (measurable, probability measures carried by $[0,1]$) is part of the good event; reason: it makes the source's implicit claim explicit and ensures the joint law is the true one.
--   - encoding: finite class $\mathcal G$ → `G : Finset (X → ℝ)` with $|\mathcal G|$ its cardinality; reason: a finite set of functions, so no test is counted twice.
--   - reading: a finite class G with no explicit nonemptiness assumption, leaving log(0) unspecified → G = ∅ is permitted, MA = 0 and Real.log 0 = 0; reason: this extends the formula at the undefined empty-class boundary; the calibration guarantee still follows using the lifted tests alone.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 18, Theorem 4.1 (Algorithm 1, p. 18; proof pp. 19–20)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Setting
import Definitions.Def_CalibratedMA_Randomized_Algorithm1

open MeasureTheory

universe u

namespace CalibratedMA.Randomized

/-- Theorem 4.1 (p. 18), randomized upper bound for calibrated multiaccuracy. There is a
universal `C` such that for every measurable space `X`, every distribution `D` on `X × [0,1]`,
every finite class `G` of measurable `g : X → [−1,1]`, every `n ≥ 2` and `δ ∈ (0, 1/2)`, the
`n`-sample probability that Algorithm 1 fails to return a randomized predictor `Q` with
`CMA(Q; G) ≤ C (√(log(2|G|/δ)/n) + (log(2n/δ)/n)^{2/5})` is at most `δ`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D],
        (∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1) →
        ∀ G : Finset (X → ℝ), (∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) →
        ∀ n : ℕ, 2 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
          (Measure.pi fun _ : Fin n => D)
              {ω | ¬ (IsRandomizedPredictor (algorithm1 n δ G ω) ∧
                  CMA D (algorithm1 n δ G ω) G ≤
                    C * (Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
                      (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)))} ≤
            ENNReal.ofReal δ := by sorry

end CalibratedMA.Randomized
