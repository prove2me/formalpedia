-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_sample_sizes_same_order
-- name    : BOLDSelect.Balance.bold_sample_sizes_same_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:22.034247+00:00
-- url     : https://prove2.me/theorems/e23fd17e-3a09-473a-9a49-292a31c79d99
-- title:
--   Theorem 2 — under BOLD, $\limsup_n N^n_x/N^n_y < \infty$ for any two alternatives, almost surely
-- statement:
--   In the setting of Theorem 1 ($M > 2$ alternatives with distinct means, distributional families whose rate functions satisfy Assumptions 1–3 with intervals $H_x$ and the parameter-space convention, an observation array on $(\Omega,P)$, any initial means $\theta^0_x \in \Theta_x$, and any allocation that is a run of BOLD on every realization), with probability 1, for any two alternatives $x$ and $y$,
--   $$\limsup_{n\to\infty} \frac{N^n_x}{N^n_y} < \infty.$$
--
--   All sample sizes therefore grow at the same order: BOLD assigns a number of samples of order $n$ to every alternative. This is the second step of the analysis, after consistency, and it is used to control the plug-in rate estimates in the proofs of the balance conditions.
--
--   **Formalization Note** "With probability 1" comes from the opening of §4. The quotient and the limit superior are taken in $[0,\infty]$, where $N/0 = \infty$ for $N > 0$ and $0/0 = 0$; thus the statement is exactly that the ratios are eventually bounded by a finite constant, which may depend on the realization. The statement holds for every BOLD run (every tie-breaking rule). The parameter-space convention and $\theta^0_x \in \Theta_x$ are not printed; they read "$\theta^0_x$ chosen arbitrarily" as arbitrary within the parameter space. Without them the statement fails (see the Assumptions file), and they exclude Bernoulli laws, whose sample means can reach $0$ or $1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3374, Theorem 2

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- Theorem 2 (p. 3374): under Assumptions 1–3, almost surely, for any two alternatives `x, y`,
`limsup_{n→∞} N^n_x / N^n_y < ∞` (the ratio and the `limsup` taken in `[0, ∞]`). -/
theorem bold_sample_sizes_same_order
    {M : ℕ} (hM : 2 < M) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (W : Fin M → ℕ → Ω → ℝ) (hW : ObsArray P (fun x => Fam x (μ x)) W)
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (X : ℕ → Ω → Fin M)
    (hX : ∀ ω, IsBOLD Fam θ0 (fun x k => W x k ω) (fun n => X n ω)) :
    ∀ᵐ ω ∂P, ∀ x y : Fin M,
      limsup (fun n =>
        (sampleCount (fun m => X m ω) n x : ℝ≥0∞) /
          (sampleCount (fun m => X m ω) n y : ℝ≥0∞)) atTop < ⊤ := by sorry

end BOLDSelect.Balance
