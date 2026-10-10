-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonPanjerStep_unique_sequences
-- name    : ActuarialValuation.compoundPoissonPanjerStep_unique_sequences
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T16:30:52.127784+00:00
-- url     : https://prove2.me/theorems/b360cf96-ffb7-4737-9ef4-1721b4aa8078
-- title:
--   Unique finite-horizon sequence determined by Panjer's positive-index recursion
-- statement:
--   Two real-valued aggregate coefficient sequences having the same initial coefficient and satisfying the same strictly-positive-index Panjer recurrence agree at every loss size. Strong induction applies because the j=0 term has zero multiplier, while for j>0 the residual loss s-j is strictly smaller than s. This is an independent uniqueness ingredient for the mission's compound-Poisson Panjer theorem and holds for arbitrary real rate and severity coefficients.
-- source:
--   Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, DOI 10.1017/S0515036100006796. Statement is a derived algebraic uniqueness lemma for the discrete Panjer recursion.

import Mathlib
import Definitions.Def_actuarial_compoundPoissonPanjerStep

namespace ActuarialValuation

theorem compoundPoissonPanjerStep_unique_sequences
  (rate : ℝ) (f g h : ℕ → ℝ)
  (hbase : g 0 = h 0)
  (hg : ∀ s : ℕ, g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1))
  (hh : ∀ s : ℕ, h (s + 1) = compoundPoissonPanjerStep rate f h (s + 1)) :
  ∀ s : ℕ, g s = h s := by sorry

end ActuarialValuation
