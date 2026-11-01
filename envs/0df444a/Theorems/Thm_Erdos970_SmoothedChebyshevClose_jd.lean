-- Prove2me | Theorems.Thm_Erdos970_SmoothedChebyshevClose_jd
-- name    : Erdos970.SmoothedChebyshevClose_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:19:51.450119+00:00
-- url     : https://prove2.me/theorems/e8994b59-d428-402e-ab08-0850bba61369
-- title:
--   Erdos970.SmoothedChebyshevClose_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970`, with `open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real`, `open _root_.ArithmeticFunction (vonMangoldt)`, `open ComplexConjugate`, `open _root_.MeasureTheory`):
--
--   ```lean
--   theorem SmoothedChebyshevClose_jd {SmoothingF : ℝ → ℝ}
--       (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
--       (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
--       (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
--       (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
--       ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
--       ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.ChebyshevPsi` and `Erdos970.SmoothedChebyshev` (definitions bundle `OAIQ083J000` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

theorem SmoothedChebyshevClose_jd {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  sorry

open _root_.Filter Topology

end Erdos970
end
