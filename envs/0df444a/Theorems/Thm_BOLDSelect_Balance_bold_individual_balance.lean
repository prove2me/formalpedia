-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_individual_balance
-- name    : BOLDSelect.Balance.bold_individual_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:34.442746+00:00
-- url     : https://prove2.me/theorems/df7eb107-a67d-4748-92ec-212ef1f3708d
-- title:
--   Theorem 4 — BOLD satisfies the individual balance conditions (6) asymptotically, almost surely
-- statement:
--   In the setting of Theorem 3 ($M > 2$ alternatives with distinct means and best alternative $x^*$, distributional families whose rate functions satisfy Assumptions 1–4 with intervals $H_x$ and the parameter-space convention, an observation array on $(\Omega,P)$, any initial means $\theta^0_x \in \Theta_x$, any allocation that is a run of BOLD on every realization), write
--   $$\Gamma^n_{x^*,y} = N^n_{x^*} I^n_{x^*}(u^n_{x^*,y}) + N^n_y I^n_y(u^n_{x^*,y})$$
--   for the rescaled approximate rate (11). Then, with probability 1, for any $y, z \neq x^*$,
--   $$\lim_{n\to\infty}\frac{\Gamma^n_{x^*,y}}{\Gamma^n_{x^*,z}} = 1.$$
--
--   This is the plug-in form of the individual balance conditions (6), the second half of the Glynn–Juneja optimality conditions: the estimated large-deviations rates of all pairwise comparisons between $x^*$ and a suboptimal alternative become equal.
--
--   **Formalization Note** "With probability 1" comes from the opening of §4. $\Gamma$ and the quotient are taken in $[0,\infty]$ ($0\cdot\infty = 0$, $a/0=\infty$ for $a>0$, $0/0 = \infty/\infty = 0$); since the $\Gamma^n$ are eventually positive and finite on almost every path, these conventions do not make the statement easier. The statement holds for every BOLD run (every tie-breaking rule). The parameter-space convention and $\theta^0_x \in \Theta_x$ are not printed; they read "$\theta^0_x$ chosen arbitrarily" as arbitrary within the parameter space. Without them the statement fails (see the Assumptions file), and they exclude Bernoulli laws, whose sample means can reach $0$ or $1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3375, Theorem 4

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- Theorem 4 (p. 3375): under Assumptions 1–4, almost surely, for any `y, z ≠ x*`,
`Γ^n_{x*,y} / Γ^n_{x*,z} → 1`: the individual balance conditions (6) hold asymptotically. -/
theorem bold_individual_balance
    {M : ℕ} (hM : 2 < M) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (xstar : Fin M) (hxstar : ∀ x, x ≠ xstar → μ x < μ xstar)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (hA4 : Assumption4 Fam)
    (W : Fin M → ℕ → Ω → ℝ) (hW : ObsArray P (fun x => Fam x (μ x)) W)
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (X : ℕ → Ω → Fin M)
    (hX : ∀ ω, IsBOLD Fam θ0 (fun x k => W x k ω) (fun n => X n ω)) :
    ∀ᵐ ω ∂P, ∀ y z : Fin M, y ≠ xstar → z ≠ xstar →
      Tendsto (fun n =>
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar y /
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar z) atTop (𝓝 1) := by sorry

end BOLDSelect.Balance
