-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonPanjerStep_nonneg
-- name    : ActuarialValuation.compoundPoissonPanjerStep_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:32:50.98009+00:00
-- url     : https://prove2.me/theorems/e6fcb50d-32f1-42c2-a1e6-9e11192c3c28
-- title:
--   Panjer update preserves nonnegative aggregate coefficients
-- statement:
--   For a positive integer aggregate loss, the Poisson rate divided by claim size is nonnegative. Every weighted summand j f(j) g(s-j) is also nonnegative, so the recursive Panjer coefficient is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \lambda,f,g\ge0,\ s>0\Longrightarrow P_\lambda(f,g;s)\ge0
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonPanjerStep

namespace ActuarialValuation

theorem compoundPoissonPanjerStep_nonneg
  (rate : ℝ) (f g : ℕ → ℝ) (s : ℕ)
  (hr : 0 ≤ rate) (hs : 0 < s)
  (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j) :
  0 ≤ compoundPoissonPanjerStep rate f g s := by sorry

end ActuarialValuation
