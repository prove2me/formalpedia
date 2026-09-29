-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
-- name    : BanditAlgorithm.gittins_stopping_ratio_le_index
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T02:54:56.102583+00:00
-- url     : https://prove2.me/theorems/90d700dd-8f06-44b7-9845-d0f78dddccd0
-- title:
--   Stopping-time reward ratios are bounded by the Gittins index
-- statement:
--   Let $(S_t)_{t\ge 0}$ be a Markov chain with transition kernel $P$, started from state $x$, measurable reward function $r:S\to\mathbb R$, and discount factor $\alpha\in(0,1)$. Assume the expected infinite discounted sum of absolute rewards is finite. For any stopping time $\tau\ge 1$, the expected discounted reward per expected discounted unit of time is at most the Gittins index:
--
--   $$
--   \frac{\mathbb E_x\!\left[\sum_{t<\tau}\alpha^t r(S_t)\right]}{\mathbb E_x\!\left[\sum_{t<\tau}\alpha^t\right]}
--   \le g(x).
--   $$
--
--   This is the fundamental upper-bound direction of the stopping-time characterization of the Gittins index and is reusable in prevailing-charge arguments for discounted Markov bandits.
--
--   **Formalization Note** Stopping times take values in $\mathbb N\cup\{\infty\}$ and are adapted to the natural coordinate filtration. The integrability assumption ensures the numerator is a genuine finite Bochner integral and the denominator is at least one.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), §35.4.1, printed p.448, Eq. (35.9), under Assumption 35.6 on printed p.448.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_stopping_ratio_le_index
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
          ∂markovChainMeasure P x) ≤
      gittinsIndex P r α x := by
  sorry
