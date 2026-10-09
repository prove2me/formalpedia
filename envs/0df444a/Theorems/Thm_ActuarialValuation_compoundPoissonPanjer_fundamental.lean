-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonPanjer_fundamental
-- name    : ActuarialValuation.compoundPoissonPanjer_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:36:17.33073+00:00
-- url     : https://prove2.me/theorems/f47aa19e-1c78-48a1-bf2d-b2e23e6a2170
-- title:
--   Compound Poisson Panjer identity and recurrence uniqueness
-- statement:
--   The fundamental theorem gives the exact zero-claim probability, Panjer's recursive computation for each strictly positive aggregate amount, and uniqueness of the sequence satisfying that recurrence. Positive severities are crucial; no silent omission of zero-sized claims is allowed.
--
--   **Mathematical statement**
--
--   $$
--   g_0=e^{-\lambda},\quad g_{s+1}=\frac{\lambda}{s+1}\sum_{j=1}^{s+1}jf_jg_{s+1-j},\quad\text{unique}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonPanjerStep

namespace ActuarialValuation

theorem compoundPoissonPanjer_fundamental
  (rate : ℝ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
  (compoundPoissonAggregatePMF rate f 0 = Real.exp (-rate)) ∧
  (∀ s : ℕ, compoundPoissonAggregatePMF rate f (s + 1) =
    compoundPoissonPanjerStep rate f
      (compoundPoissonAggregatePMF rate f) (s + 1)) ∧
  (∀ g : ℕ → ℝ, g 0 = Real.exp (-rate) →
    (∀ s : ℕ, g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1)) →
    ∀ s : ℕ, g s = compoundPoissonAggregatePMF rate f s) := by sorry

end ActuarialValuation
