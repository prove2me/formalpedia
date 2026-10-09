-- Prove2me | Theorems.Thm_ActuarialValuation_finiteStageBellmanMaximum_mono
-- name    : ActuarialValuation.finiteStageBellmanMaximum_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:13:00.068482+00:00
-- url     : https://prove2.me/theorems/18d17008-b3b0-474e-aa1b-6db59ee8a3ec
-- title:
--   Bellman operator monotonicity
-- statement:
--   Pointwise monotonicity of every action is preserved by the finite maximum.
--
--   **Mathematical statement**
--
--   $$
--   U\le W\Rightarrow TU\le TW
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageBellmanMaximum
open MeasureTheory

namespace ActuarialValuation

theorem finiteStageBellmanMaximum_mono {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (U W : S → ℝ) (s : S)
  (hP : ∀ a t, 0 ≤ P s a t) (hv : 0 ≤ v)
  (hUW : ∀ t, U t ≤ W t)
  :
  finiteStageBellmanMaximum P reward v U s ≤ finiteStageBellmanMaximum P reward v W s := by sorry

end ActuarialValuation
