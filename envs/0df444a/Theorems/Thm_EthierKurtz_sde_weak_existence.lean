-- Prove2me | Theorems.Thm_EthierKurtz_sde_weak_existence
-- name    : EthierKurtz.sde_weak_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:54:23.862875+00:00
-- url     : https://prove2.me/theorems/d55a7ea5-cc9f-403a-b23a-e3700f54dcd6
-- title:
--   Theorem 3.10 — weak existence with continuous coefficients
-- statement:
--   Continuous diffusion and drift coefficients satisfying the stated one-sided linear growth inequalities admit a weak Brownian stochastic integral equation solution for every initial probability law.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, Theorem 3.10, printed p. 299 (PDF p. 308), equation (3.33).

import Definitions.Def_EthierKurtz_IsWeakSDESolution

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- A solution exists on some probability space with some Brownian driver.
The drift bound is one-sided, not a bound on its norm. The initial law is
arbitrary; no moment, Lipschitz, nondegeneracy, or uniqueness assumption is made. -/
theorem sde_weak_existence
    {d : ℕ}
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (hσ : Continuous σ) (hb : Continuous b)
    (hgrowth : ∃ K : ℝ, ∀ (t : ℝ≥0) (x : SDEState d),
      ‖σ (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2) ∧
      (∑ i, x i * b (t, x) i) ≤ K * (1 + ‖x‖ ^ 2))
    (μ : Measure (SDEState d)) [IsProbabilityMeasure μ] :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ (ℱ : Filtration ℝ≥0 m) (W X : ℝ≥0 → Ω → SDEState d),
          IsWeakSDESolution P ℱ σ b μ W X := by sorry
