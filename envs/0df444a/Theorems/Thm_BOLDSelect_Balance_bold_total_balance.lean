-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_total_balance
-- name    : BOLDSelect.Balance.bold_total_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:22.546988+00:00
-- url     : https://prove2.me/theorems/2713b663-3604-4fb1-8b06-45c61ec9843c
-- title:
--   Theorem 3 — BOLD satisfies the total balance condition (5) asymptotically, almost surely
-- statement:
--   Let there be $M > 2$ alternatives with distinct true means $\mu_x$, and let $x^*$ be the alternative with the largest mean. Alternative $x$ samples from the law $F_x(\mu_x)$ of its distributional family, whose rate functions satisfy Assumptions 1–4 with intervals $H_x = [a_x,b_x]$ containing $\mu_x$ in their interior, together with the parameter-space convention (open intervals $\Theta_x \supseteq H_x$ that contain the samples almost surely, on which the family has mean $\theta$ and finite rate functions between parameters). Let $(W_{x,k})$ be an observation array on $(\Omega,P)$, $\theta^0$ any initial means with $\theta^0_x \in \Theta_x$, and $x^n(\omega)$ any allocation that is a run of BOLD on every realization. Write $I^n_x(\cdot) = I_x(\cdot;\theta^n_x)$ and let $u^n_{x^*,x}$ be the solution of $N^n_{x^*}D^n_{x^*}(u) + N^n_x D^n_x(u) = 0$ (equation (10)). Then, with probability 1,
--   $$\lim_{n\to\infty}\sum_{x\neq x^*}\frac{I^n_{x^*}(u^n_{x^*,x})}{I^n_x(u^n_{x^*,x})} = 1.$$
--
--   The sum is the plug-in version of the left side of the total balance condition (5), the first half of the Glynn–Juneja optimality conditions for the asymptotically optimal static allocation; BOLD's Step 2 compares exactly this quantity (with the current leader in place of $x^*$) to 1.
--
--   **Formalization Note** "With probability 1" comes from the opening of §4. The sum uses the true best $x^*$, not the current leader $x^{*,n}$. Quotients are taken in $[0,\infty]$ ($a/0 = \infty$ for $a>0$, $0/0 = \infty/\infty = 0$), and the limit is in $[0,\infty]$; these conventions affect only finitely many stages and can only make the convergence harder, not easier. The statement holds for every BOLD run (every tie-breaking rule). The parameter-space convention and $\theta^0_x \in \Theta_x$ are not printed; they read "$\theta^0_x$ chosen arbitrarily" as arbitrary within the parameter space. Without them the statement fails (see the Assumptions file), and they exclude Bernoulli laws, whose sample means can reach $0$ or $1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3374, Theorem 3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- Theorem 3 (p. 3374): under Assumptions 1–4, almost surely
`∑_{x ≠ x*} I^n_{x*}(u^n_{x*,x}) / I^n_x(u^n_{x*,x}) → 1`: the total balance condition (5) holds
asymptotically. -/
theorem bold_total_balance
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
        (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar) atTop (𝓝 1) := by sorry

end BOLDSelect.Balance
