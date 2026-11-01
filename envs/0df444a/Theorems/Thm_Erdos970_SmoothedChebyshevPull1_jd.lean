-- Prove2me | Theorems.Thm_Erdos970_SmoothedChebyshevPull1_jd
-- name    : Erdos970.SmoothedChebyshevPull1_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:20:51.772202+00:00
-- url     : https://prove2.me/theorems/135c7be9-48c1-4e5f-9daa-baed1b684f31
-- title:
--   Erdos970.SmoothedChebyshevPull1_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970`, with `open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real`, `open _root_.ArithmeticFunction (vonMangoldt)`, `open ComplexConjugate`, `open _root_.MeasureTheory`):
--
--   ```lean
--   theorem SmoothedChebyshevPull1_jd {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
--       (ε_lt_one : ε < 1)
--       (X : ℝ) (X_gt : 3 < X)
--       {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
--       (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
--       (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
--       (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
--       (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
--       (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
--       (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
--       SmoothedChebyshev SmoothingF ε X =
--         I₁ SmoothingF ε X T -
--         I₂ SmoothingF ε T X σ₁ +
--         I₃₇ SmoothingF ε T X σ₁ +
--         I₈ SmoothingF ε T X σ₁ +
--         I₉ SmoothingF ε X T
--         + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.HolomorphicOn`, `Erdos970.I₁`, `Erdos970.I₂`, `Erdos970.I₃₇`, `Erdos970.I₈`, `Erdos970.I₉`, `Erdos970.MellinTransform`, `Erdos970.Smooth1` and `Erdos970.SmoothedChebyshev` (definitions bundle `OAIQ083J000` of this split).
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

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

theorem SmoothedChebyshevPull1_jd {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  sorry

open _root_.Filter Topology

end Erdos970
end
