-- Prove2me | Theorems.Thm_BanditAlgorithm_klDiv_stopped_le_iSup_truncations
-- name    : BanditAlgorithm.klDiv_stopped_le_iSup_truncations
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:48:55.247431+00:00
-- url     : https://prove2.me/theorems/36223a6e-e7ca-4163-8454-b0497fe35b18
-- title:
--   Stopped relative entropy is approximated by bounded stopping times
-- statement:
--   Run the same adaptive bandit policy in two environments, producing trajectory laws $P$ and $Q$, and let $\tau$ be a stopping time with finite expectation under $P$. Write $\mathcal F_\tau$ for the stopped sigma-algebra and $\tau_n=\min\{\tau,n\}$. Then the relative entropy of the stopped experiment is bounded by the supremum of the relative entropies of its bounded truncations:
--
--   $$
--   D\!\left(P|_{\mathcal F_\tau}\,\middle\Vert\,Q|_{\mathcal F_\tau}\right)
--   \le
--   \sup_{n\ge0}D\!\left(P|_{\mathcal F_{\tau_n}}\,\middle\Vert\,Q|_{\mathcal F_{\tau_n}}\right).
--   $$
--
--   This is the measure-theoretic truncation principle needed to pass finite-horizon likelihood calculations to an integrable, possibly unbounded stopping time. It is useful beyond best-arm identification whenever an adaptive experiment is observed at a random horizon.
--
--   **Formalization Note** The trajectory measures are restricted with `Measure.trim` to Mathlib's stopped measurable spaces. The supremum is represented as an `ENNReal` indexed supremum.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211, truncation step extending Lemma 15.1 to stopping times; stopped sigma-algebra formulation as used in Chapter 33, Section 33.2.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.klDiv_stopped_le_iSup_truncations
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace
        ((banditTrajMeasure ν π).trim hτ.measurableSpace_le)
        ((banditTrajMeasure ν' π).trim hτ.measurableSpace_le) ≤
      ⨆ n : ℕ,
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
          ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) := by
  sorry
