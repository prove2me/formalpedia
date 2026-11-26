-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_discounted_cost_of_queue_coupling
-- name    : BellWilliams2001.ThresholdPolicy.discounted_cost_of_queue_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:34:25.801575+00:00
-- url     : https://prove2.me/theorems/ae008391-adae-4e7e-942d-cd72e33577c6
-- title:
--   State coupling and polynomial second moments give convergence of discounted costs
-- statement:
--   Suppose a sequence of admissible allocations has the coupling of queue lengths and idle times in Theorem 5.2, and suppose its instantaneous holding-cost second moments are bounded by $C(1+t)^p$ uniformly in all large system indices and all diffusion times $t\ge0$. Then the expected discounted costs converge to $J^*$, which is finite.
--
--   At each time the coupling gives almost-sure convergence of the coupled holding costs. Uniform integrability then gives convergence of their expectations. Exponential discounting makes the polynomial expectation bound integrable over time.
-- source:
--   Bell and Williams (2001), The Annals of Applied Probability 11(3), 608–649, https://doi.org/10.1214/aoap/1015345343, Section 9, passage from state-space collapse and the moment bounds to convergence of expected discounted costs

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem discounted_cost_of_queue_coupling {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ᶠ n in atTop, M.IsAdmissible n (T n))
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B)
    (hCouple : CouplingConverges M.P P'
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Qhat n (T n) ω t 1,
        M.Ihat n (T n) ω t 0, M.Ihat n (T n) ω t 1])
      (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]))
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hMom : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
      (∫⁻ ω, (ENNReal.ofReal (∑ k, M.h k * M.Qhat n (T n) ω t k)) ^ 2 ∂M.P) ≤
        ENNReal.ofReal (C * (1 + t) ^ p)) :
    Tendsto (fun n => M.cost n (T n)) atTop (𝓝 (M.Jstar P' B)) ∧ M.Jstar P' B < ⊤ := by sorry

end BellWilliams2001.ThresholdPolicy
