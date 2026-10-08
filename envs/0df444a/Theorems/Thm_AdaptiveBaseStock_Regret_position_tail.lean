-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_position_tail
-- name    : AdaptiveBaseStock.Regret.position_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:14.465935+00:00
-- url     : https://prove2.me/theorems/ddb1856a-e36c-48f1-b9b9-8855a73e2ca7
-- title:
--   Lemma 6 — P[X_t(S)·1^τ > S | X₁ = x₁] ≤ F(x₁·1^τ − S)^{t−τ}
-- statement:
--   Consider the lost-sales system with lead time $\tau \ge 1$ and i.i.d. continuous demand of infinite support, operated under the order-up-to-$S$ policy with $S \ge 0$ from an initial inventory vector $x_1 \in \mathbb R^\tau_+$. Then for every period $t \ge \tau$,
--   $$\mathcal P\big[X_t(S)\cdot \mathbf 1^\tau > S \,\big|\, X_1(S) = x_1\big] \le F(x_1\cdot \mathbf 1^\tau - S)^{t-\tau}.$$
--
--   The inventory position can exceed $S$ only while the initial excess has not been consumed, so this bounds the transient phase of the chain; together with the coalescence bound it yields the ergodicity rate of Theorem 3.
--
--   **Formalization Note** The conditioning on $X_1(S) = x_1$ is a deterministic start. Lean period $t$ is the paper's period $t+1$, so the paper's $t \ge \tau$ reads $\tau \le t+1$ and the exponent $t - \tau$ reads $t + 1 - \tau$. Only the infinite-support case of the paper's lemma is stated.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 6 (first case), p. 16

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (infinite-support case), p. 16: under the order-up-to-`S` policy started from
`x₁ ∈ ℝ^τ_+`, `P[X_t(S) · 1^τ > S] ≤ F(x₁ · 1^τ - S)^{t-τ}` for every period `t ≥ τ`. Lean period
`t` is the paper's period `t + 1`, so the paper's `t ≥ τ` reads `τ ≤ t + 1` and its exponent
`t - τ` reads `t + 1 - τ`. -/
theorem position_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (S : ℝ) (hS : 0 ≤ S) (x₁ : InvVec τ) (hx₁ : IsNonneg x₁)
    (t : ℕ) (ht : τ ≤ t + 1) :
    P.real {ω | S < position (run (fun _ => S) x₁ (fun n => D n ω) t)}
      ≤ demandCdf P (D 0) (position x₁ - S) ^ (t + 1 - τ) := by sorry

end AdaptiveBaseStock.Regret
