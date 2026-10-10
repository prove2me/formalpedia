-- Prove2me | Theorems.Thm_ActuarialValuation_finiteStageActionReturn_mono
-- name    : ActuarialValuation.finiteStageActionReturn_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:10:46.833704+00:00
-- url     : https://prove2.me/theorems/ec945e20-a890-4c53-a148-4763717702b9
-- title:
--   Nonnegative transition weights preserve action-value order
-- statement:
--   Higher continuation values cannot reduce an action's discounted reward if discount and weights are nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   U\le W\Rightarrow Q(U)\le Q(W)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
open MeasureTheory

namespace ActuarialValuation

theorem finiteStageActionReturn_mono {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (U W : S → ℝ) (s : S) (a : A)
  (hP : ∀ t, 0 ≤ P s a t) (hv : 0 ≤ v)
  (hUW : ∀ t, U t ≤ W t)
  :
  finiteStageActionReturn P reward v U s a ≤ finiteStageActionReturn P reward v W s a := by sorry

end ActuarialValuation
