-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_long_run_cost
-- name    : AdaptiveBaseStock.Regret.long_run_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:23.931975+00:00
-- url     : https://prove2.me/theorems/a5d25b71-7930-4964-b6c0-ca5a4bfc7482
-- title:
--   Theorem 7 — the long-run average cost C(I_∞(S)) exists, is independent of X₁, convex and differentiable in S, and has a minimizer S* with γ(S*) > 0
-- statement:
--   Consider the lost-sales system with lead time $\tau \ge 1$, holding cost $h > 0$, lost-sales penalty $b > 0$ and i.i.d. nonnegative continuous demand with $E[D] > 0$. For every $S \ge 0$:
--
--   1. for every initial inventory vector $x_1 \in \mathbb R^\tau_+$ the average cost $\frac1T \sum_{t=1}^T E[C(I_t(S))]$ converges, and its limit $C(I_\infty(S))$ is the same for every $x_1$;
--   2. if $\gamma(S) = 0$, then $C(I_\infty(S)) = b\,\big(E[D] - \frac{S}{\tau+1}\big)$;
--   3. if $\gamma(S) > 0$, then there is a steady-state law of the inventory vector, and
--   $$C(I_\infty(S)) = b\, E[D - I_\infty(S)]^+ + h\, E[I_\infty(S) - D]^+,$$
--   where $I_\infty(S)$ is the on-hand inventory under that law and $D$ is an independent demand.
--
--   Moreover the function $S \mapsto C(I_\infty(S))$ is convex and differentiable on $[0,\infty)$, and it has a minimizer $S^* \ge 0$ with $\gamma(S^*) > 0$.
--
--   This theorem identifies the objective that the adaptive algorithm minimizes, establishes the convexity that its gradient steps rely on, and shows that the benchmark $S^*$ of the regret exists.
--
--   **Formalization Note** The steady-state expectation is written as $\int C(x_\tau)\, d\pi(x)$, which equals $b\,E[D - I_\infty]^+ + h\,E[I_\infty - D]^+$ for a demand independent of $I_\infty$. Differentiability on $[0,\infty)$ is one-sided at $S = 0$. The long-run cost of the model is a `limsup` from the empty start, so item 1 states that the limit exists from every start and equals it.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Theorem 7, p. 18

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 7, p. 18: for every `S ≥ 0` the long-run average cost of the order-up-to-`S` policy
exists and does not depend on the initial inventory vector; it equals `b · (E[D] - S/(τ+1))` when
`γ(S) = 0` and `E[C(I_∞(S))]` for a steady-state law when `γ(S) > 0`; as a function of `S ≥ 0`
it is convex and differentiable, and it has a minimizer `S*` with `γ(S*) > 0`. -/
theorem long_run_cost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (τ : ℕ) (hτ : 1 ≤ τ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) :
    (∀ S : ℝ, 0 ≤ S → ∀ x₁ : InvVec τ, IsNonneg x₁ →
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          ∫ ω, periodCost P (D 0) h b (run (fun _ => S) x₁ (fun n => D n ω) t).2 ∂P)
        atTop (nhds (baseStockCost P D τ h b S))) ∧
    (∀ S : ℝ, 0 ≤ S → gammaLevel P (D 0) τ S = 0 →
      baseStockCost P D τ h b S = b * ((∫ ω, D 0 ω ∂P) - S / ((τ : ℝ) + 1))) ∧
    (∀ S : ℝ, 0 ≤ S → 0 < gammaLevel P (D 0) τ S →
      ∃ π : Measure (InvVec τ), IsSteadyStateLaw P D τ S π ∧
        baseStockCost P D τ h b S = ∫ x, periodCost P (D 0) h b x.2 ∂π) ∧
    ConvexOn ℝ (Set.Ici 0) (baseStockCost P D τ h b) ∧
    DifferentiableOn ℝ (baseStockCost P D τ h b) (Set.Ici 0) ∧
    ∃ Sstar : ℝ, 0 ≤ Sstar ∧ IsMinOn (baseStockCost P D τ h b) (Set.Ici 0) Sstar ∧
      0 < gammaLevel P (D 0) τ Sstar := by sorry

end AdaptiveBaseStock.Regret
