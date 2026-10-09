-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_utility_nonneg
-- name    : BalancedPrices.WeakExtension.utility_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:49.246806+00:00
-- url     : https://prove2.me/theorems/f7d7308b-5da6-4ef9-90c3-db9c2c85dc9d
-- title:
--   Appendix A, Case 1, p. 560 — every agent's utility uᵢ(v) in the posted-price run is nonnegative
-- statement:
--   Consider $n$ agents with outcome spaces $X_i$ containing a null outcome $\emptyset$, a downward-closed feasible set $\mathcal F$ containing the all-null profile, countable type spaces $V_i$ with independent distributions $\mathcal D_i$, and valuations $\mathrm{val}_i(w,\cdot)$ with values in $[0,1]$. Let $(p^{\tilde v})_{\tilde v\in V}$ be pricing rules (prices are $\infty$ on infeasible additions) under which the null outcome is free at every feasible partial allocation, $p^{\tilde v}_i(\emptyset\mid y) = 0$ for $y\in\mathcal F$. Let $\delta>0$ and let the agents choose utility-maximizing outcomes under the posted prices $\delta\,p_i(x_i\mid y)$, where $p_i(x_i\mid y) = \mathbb E_{\tilde v}[p^{\tilde v}_i(x_i\mid y)]$. Then for every type profile $v$ and every agent $i$,
--   $$u_i(v) \ \ge\ 0,$$
--   where $u_i(v)$ is agent $i$'s utility in the run of the posted-price mechanism.
--
--   In the proof of Theorem 3.5 this is what allows the utilities to be scaled down by $\rho = 1/(2\alpha\beta_2)\le 1$ in Case 1 ($u_i(v)\ge\rho\,u_i(v)$).
--
--   **Formalization Note.** The page uses $u_i(v)\ge0$ without stating why. It holds because the null outcome is free and remains feasible after any feasible prefix, so an agent can always secure utility $v_i(\emptyset)\ge 0$; the hypothesis `hnull` (null outcome free) is the paper's standing convention made explicit — every pricing rule in the paper satisfies it. `hnF : nul ∈ F` holds in the paper because $\mathcal F$ is downward closed and nonempty. The scaling $\delta$ is an arbitrary positive real here; Theorem 3.5 uses $\delta = 1/(\beta_1+\max\{2\beta_2,1/\alpha\})$. Agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, Appendix A (proof of Theorem 3.5), Combination, Case 1, first sentence

import Mathlib
import Definitions.Def_BalancedPrices_WeakExtension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open MeasureTheory

namespace BalancedPrices.WeakExtension

theorem utility_nonneg
    {n : ℕ} {X V : Fin n → Type*}
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (μ i)]
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X)) (hF : BalancedPrices.Extension.DownClosed nul F)
    (val : ∀ i, V i → X i → ℝ) (hval : ∀ i w xi, 0 ≤ val i w xi ∧ val i w xi ≤ 1)
    (hnF : nul ∈ F)
    (pv : (∀ i, V i) → BalancedPrices.Extension.PriceRule X)
    (hrule : ∀ w, BalancedPrices.Extension.IsPricingRule F (pv w))
    (hnull : ∀ w i y, y ∈ F → pv w i (nul i) y = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (choice : ∀ i, V i → BalancedPrices.Extension.Outcome X → X i)
    (hchoice : BalancedPrices.Extension.IsUtilMax F val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice) :
    ∀ v i, 0 ≤ BalancedPrices.Extension.utility nul val (fun i xi y => ENNReal.ofReal δ * BalancedPrices.Extension.expPrice μ pv i xi y) choice v i := by sorry

end BalancedPrices.WeakExtension
