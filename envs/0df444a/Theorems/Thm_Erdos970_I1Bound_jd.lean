-- Prove2me | Theorems.Thm_Erdos970_I1Bound_jd
-- name    : Erdos970.I1Bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:19:37.89239+00:00
-- url     : https://prove2.me/theorems/32011d84-b6b8-4018-b244-e2f3df4ea3f2
-- title:
--   Erdos970.I1Bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970`, with `open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real`, `open _root_.ArithmeticFunction (vonMangoldt)`, `open ComplexConjugate`, `open _root_.MeasureTheory`):
--
--   ```lean
--   theorem I1Bound_jd
--       {SmoothingF : ℝ → ℝ}
--       (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
--       (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
--       (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
--       ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
--       (_ : ε < 1)
--       (X : ℝ) (_ : 3 < X)
--       {T : ℝ} (_ : 3 < T),
--       ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.I₁` (definitions bundle `OAIQ083J000` of this split).
--
--   **Used by.** The proofs of `Erdos970.I9Bound_jd` and `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd` of this split import it.
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

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

theorem I1Bound_jd
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  sorry

open _root_.Filter Topology

end Erdos970
end
