-- Prove2me | Theorems.Thm_BOLDSelect_Balance_bold_consistency
-- name    : BOLDSelect.Balance.bold_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:18.089818+00:00
-- url     : https://prove2.me/theorems/2c69be01-d247-43d7-8a88-5c8e3301bb84
-- title:
--   Theorem 1 — under BOLD every alternative is sampled infinitely often, almost surely
-- statement:
--   Let there be $M > 2$ alternatives with distinct true means $\mu_x$. Alternative $x$ samples from the law $F_x(\mu_x)$ of its distributional family, whose rate function $I_x(u;\theta)$ and derivative $D_x(u;\theta)$ satisfy Assumptions 1–3 with intervals $H_x = [a_x,b_x] \ni \mu_x$ (in their interior), together with the parameter-space convention (open intervals $\Theta_x \supseteq H_x$ that contain the samples almost surely, on which the family has mean $\theta$ and finite rate functions between parameters). Let $(W_{x,k})$ be an observation array on a probability space $(\Omega,P)$, let $\theta^0$ be any initial vector of means with $\theta^0_x \in \Theta_x$, and let $x^n(\omega)$ be any allocation that is a run of BOLD on every realization $\omega$. Then, with probability 1, for every alternative $x$,
--   $$\lim_{n\to\infty} N^n_x = \infty.$$
--
--   This is the consistency of BOLD: no alternative is starved of samples. The rest of the analysis rests on it, since it lets the sample means converge to the true means by the strong law of large numbers, after which the leader $x^{*,n}$ is eventually the true best $x^*$.
--
--   **Formalization Note** "With probability 1" is not printed in Theorem 1; it comes from the opening of §4 ("BOLD learns the solution to (5)-(6), with probability 1"). The statement holds for every BOLD run, i.e. for every tie-breaking rule, and does not require the allocation to be measurable. Only Assumptions 1–3 are assumed, as printed; "for all $x$" includes the best alternative. The parameter-space convention and $\theta^0_x \in \Theta_x$ are not printed; they read "$\theta^0_x$ chosen arbitrarily" as arbitrary within the parameter space. Without them the statement fails (see the Assumptions file), and they exclude Bernoulli laws, whose sample means can reach $0$ or $1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, p. 3374, Theorem 1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BOLDSelect.Balance

/-- Theorem 1 (p. 3374): under Assumptions 1–3, almost surely every alternative is sampled
infinitely often under BOLD: `N^n_x → ∞` for all `x`. -/
theorem bold_consistency
    {M : ℕ} (hM : 2 < M) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (W : Fin M → ℕ → Ω → ℝ) (hW : ObsArray P (fun x => Fam x (μ x)) W)
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (X : ℕ → Ω → Fin M)
    (hX : ∀ ω, IsBOLD Fam θ0 (fun x k => W x k ω) (fun n => X n ω)) :
    ∀ᵐ ω ∂P, ∀ x : Fin M,
      Tendsto (fun n => sampleCount (fun m => X m ω) n x) atTop atTop := by sorry

end BOLDSelect.Balance
