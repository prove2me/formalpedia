-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_nonneg
-- name    : ActuarialValuation.compoundPoissonAggregatePMF_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:32:19.287382+00:00
-- url     : https://prove2.me/theorems/f950cd65-8b6f-428f-adfb-43f9122497bb
-- title:
--   Nonnegative frequency and severity masses yield nonnegative aggregate mass
-- statement:
--   Poisson weights are nonnegative at every claim count for a nonnegative rate. Repeated finite convolution of nonnegative claim-severity masses remains nonnegative. Their finite weighted mixture therefore yields no negative aggregate-loss probability coefficient.
--
--   **Mathematical statement**
--
--   $$
--   \lambda\ge0,\ f\ge0\Longrightarrow g_s\ge0
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonAggregatePMF_nonneg (rate : ℝ) (f : ℕ → ℝ) (s : ℕ)
  (hr : 0 ≤ rate) (hf : ∀ k, 0 ≤ f k) :
  0 ≤ compoundPoissonAggregatePMF rate f s := by sorry

end ActuarialValuation
