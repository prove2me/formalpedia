-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_learns_optimality_conditions
-- name    : BOLDSelect.Balance.bold_learns_optimality_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:39.170976+00:00
-- url     : https://prove2.me/theorems/2e502525-2216-486c-af7a-850697568a43
-- title:
--   BOLD learns the large deviations optimality conditions (5)–(6) with probability 1 (§4 main result, Theorems 3 and 4)
-- statement:
--   Section 4 of the paper opens: "The main result is that BOLD learns the solution to (5)-(6), with probability 1, as $n \to \infty$." The result is stated in two parts: Theorem 3, "(5) is satisfied asymptotically", and Theorem 4, "(6) is satisfied asymptotically for all pairs of suboptimal alternatives". This statement is their conjunction.
--
--   Let there be $M > 2$ alternatives with distinct true means $\mu_x$, and let $x^*$ be the alternative with the largest mean. Alternative $x$ samples from the law $F_x(\mu_x)$ of its distributional family, whose large-deviations rate function $I_x(u;\theta)$ and derivative $D_x(u;\theta)$ satisfy Assumptions 1–4 with intervals $H_x = [a_x,b_x]$ containing $\mu_x$ in their interior, together with the parameter-space convention (open intervals $\Theta_x \supseteq H_x$ that contain the samples almost surely, on which the family has mean $\theta$ and finite rate functions between parameters). Let $(W_{x,k})$ be an observation array on a probability space $(\Omega,P)$, $\theta^0$ any initial means with $\theta^0_x \in \Theta_x$, and $x^n(\omega)$ any allocation that is a run of BOLD on every realization. With $I^n_x(\cdot) = I_x(\cdot;\theta^n_x)$, the solution $u^n_{x^*,x}$ of (10), and $\Gamma^n_{x^*,y} = N^n_{x^*} I^n_{x^*}(u^n_{x^*,y}) + N^n_y I^n_y(u^n_{x^*,y})$, with probability 1 both
--
--   1. the total balance condition holds in the limit:
--   $$\lim_{n\to\infty}\sum_{x\neq x^*}\frac{I^n_{x^*}(u^n_{x^*,x})}{I^n_x(u^n_{x^*,x})} = 1;$$
--   2. the individual balance conditions hold in the limit: for all $y, z \neq x^*$,
--   $$\lim_{n\to\infty}\frac{\Gamma^n_{x^*,y}}{\Gamma^n_{x^*,z}} = 1.$$
--
--   Conditions (5)–(6) characterize the optimal static allocation of Glynn and Juneja (2004), which maximizes the exponential decay rate of the probability of incorrect selection. The theorem says that BOLD, a sequential rule with no tuning parameters that only evaluates (never solves) these conditions at plug-in estimates, drives them to hold for every sampling distribution satisfying the assumptions, not only normal ones.
--
--   **Formalization Note** The probability-one qualifier comes from the §4 preamble. The theorem holds for every BOLD run, i.e. for every tie-breaking rule the paper leaves arbitrary, and for every initial vector $\theta^0$. Quotients and $\Gamma$ are taken in $[0,\infty]$ with $a/0 = \infty$ for $a>0$ and $0/0 = \infty/\infty = 0$; these conventions can only make the limits harder to reach. The solution of (10) is a chosen solution between the two sample means; the paper asserts uniqueness, which is not assumed. The parameter-space convention and $\theta^0_x \in \Theta_x$ are not printed; they read "$\theta^0_x$ chosen arbitrarily" as arbitrary within the parameter space. Without them the statement fails (see the Assumptions file), and they exclude Bernoulli laws, whose sample means can reach $0$ or $1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3373 (§4: main result), pp. 3374–3375, Theorems 3 and 4

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- The main result of §4 (p. 3373: "BOLD learns the solution to (5)-(6), with probability 1, as
`n → ∞`"), i.e. Theorems 3 and 4 jointly (pp. 3374–3375): under Assumptions 1–4, almost surely the
plug-in total balance sum tends to `1` and every ratio `Γ^n_{x*,y} / Γ^n_{x*,z}` (`y, z ≠ x*`)
tends to `1`. -/
theorem bold_learns_optimality_conditions
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
    ∀ᵐ ω ∂P,
      Tendsto (fun n => balanceSum Fam
        (sampleCount (fun m => X m ω) n)
        (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar) atTop (𝓝 1) ∧
      ∀ y z : Fin M, y ≠ xstar → z ≠ xstar →
        Tendsto (fun n =>
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar y /
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar z) atTop (𝓝 1) := by sorry

end BOLDSelect.Balance
