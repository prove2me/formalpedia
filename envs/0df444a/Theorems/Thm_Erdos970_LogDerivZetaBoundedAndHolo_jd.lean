-- Prove2me | Theorems.Thm_Erdos970_LogDerivZetaBoundedAndHolo_jd
-- name    : Erdos970.LogDerivZetaBoundedAndHolo_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:19:24.806209+00:00
-- url     : https://prove2.me/theorems/ba9143fb-85ce-4ccd-abac-22c12ea1b3f6
-- title:
--   Erdos970.LogDerivZetaBoundedAndHolo_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970`, with `open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real`, `open _root_.ArithmeticFunction (vonMangoldt)`, `open ComplexConjugate`, `open _root_.MeasureTheory`):
--
--   ```lean
--   lemma LogDerivZetaBoundedAndHolo_jd : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
--       ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
--       HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
--       (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1})
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.HolomorphicOn` and `Erdos970.LogDerivZetaHasBound` (definitions bundle `OAIQ083J000` of this split).
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

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

lemma LogDerivZetaBoundedAndHolo_jd : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  sorry

open _root_.Filter Topology

end Erdos970
end
