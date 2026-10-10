-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonPanjer_unique
-- name    : ActuarialValuation.compoundPoissonPanjer_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:35:32.916965+00:00
-- url     : https://prove2.me/theorems/fd254ae4-d36e-4ef5-8b64-1a530c1c39d8
-- title:
--   Zero-loss mass and recurrence uniquely identify the aggregate law
-- statement:
--   An arbitrary real sequence with the correct zero-loss initial mass and the Poisson Panjer coefficient recursion must coincide with the compound Poisson distribution at every aggregate loss. Induction is valid because the zero-severity term has size factor zero and every other summand uses a strictly smaller aggregate index.
--
--   **Mathematical statement**
--
--   $$
--   g_0=e^{-\lambda},\ g_{s+1}=P_\lambda(f,g;s+1)\Rightarrow g=g^{CP}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonPanjerStep

namespace ActuarialValuation

theorem compoundPoissonPanjer_unique
  (rate : ℝ) (f g : ℕ → ℝ) (hf0 : f 0 = 0)
  (h0 : g 0 = Real.exp (-rate))
  (hstep : ∀ s : ℕ,
    g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1)) :
  ∀ s : ℕ, g s = compoundPoissonAggregatePMF rate f s := by sorry

end ActuarialValuation
