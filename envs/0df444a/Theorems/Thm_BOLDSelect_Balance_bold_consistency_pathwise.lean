-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_consistency_pathwise
-- name    : BOLDSelect.Balance.bold_consistency_pathwise
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T01:11:20.303368+00:00
-- url     : https://prove2.me/theorems/793bc901-ba1f-4e47-bfd7-32837b1987eb
-- title:
--   Theorem 1, pathwise form: on every LLN path, BOLD samples every alternative infinitely often
-- statement:
--   This is the deterministic (pathwise) core of Theorem 1 of Chen & Ryzhov (WSC 2019): the consistency argument sketched after Theorem 1 works on one fixed sample path, using the law of large numbers only for alternatives that are sampled infinitely often.
--
--   Let $M>2$ alternatives have distinct true means $\mu_x$, and let the distributional families satisfy Assumptions 1–3 with intervals $H_x=[a_x,b_x]$, $a_x<\mu_x<b_x$, and the parameter-space convention (open intervals $\Theta_x\supseteq H_x$ on which the family has mean $\theta$ and finite rate functions between parameters). Fix a deterministic observation array $w_{x,k}$ (the $(k+1)$-th sample of $x$) such that
--
--   * every sample of $x$ lies in $\Theta_x$: $w_{x,k}\in\Theta_x$ for all $x,k$;
--   * the law of large numbers holds along the path for every alternative:
--   $$\frac1k\sum_{j<k} w_{x,j}\;\longrightarrow\;\mu_x\qquad(k\to\infty).$$
--
--   Let $\theta^0_x\in\Theta_x$ be arbitrary initial means and let $x^0,x^1,\dots$ be any run of BOLD (Figure 1, any tie-breaking) on this path. Then every alternative is sampled infinitely often:
--   $$\lim_{n\to\infty} N^n_x=\infty\qquad\text{for all }x.$$
--
--   This is the deterministic content of the consistency of BOLD: the paper's discussion after Theorem 1 argues on a single sample path, invoking the law of large numbers only for alternatives that are sampled infinitely often. Combined with the strong law of large numbers for each row of the observation array (and the fact that samples lie in $\Theta_x$ almost surely), it yields Theorem 1 (`BOLDSelect.Balance.bold_consistency`).
--
--   **Formalization Note** Unlike Theorem 1, no probability space appears: the path $w$ and the run $x^n$ are fixed, and the two almost-sure properties of the observation array used by the argument are hypotheses.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3374, Theorem 1 and the proof discussion following it (deterministic core of the consistency argument)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- Theorem 1 (p. 3374), pathwise form: the deterministic core of the consistency argument
sketched after Theorem 1. On a single observation path `w` along which the law of large numbers
holds for every alternative (`(1/k) ∑_{j<k} w x j → µ_x`) and every sample of `x` lies in `Θ_x`,
every run `xs` of BOLD samples every alternative infinitely often: `N^n_x → ∞` for all `x`. -/
theorem bold_consistency_pathwise
    {M : ℕ} (hM : 2 < M)
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (w : Fin M → ℕ → ℝ) (hwΘ : ∀ x k, w x k ∈ Θ x)
    (hLLN : ∀ x, Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, w x j) / (k : ℝ)) atTop
      (𝓝 (μ x)))
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (xs : ℕ → Fin M)
    (hxs : IsBOLD Fam θ0 w xs) :
    ∀ x : Fin M, Tendsto (fun n => sampleCount xs n x) atTop atTop := by sorry

end BOLDSelect.Balance
