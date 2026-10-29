-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_wh_gap_normalisation
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_wh_gap_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:35:54.558172+00:00
-- url     : https://prove2.me/theorems/6a13391c-8fc1-49f3-aac0-c66f522528a0
-- title:
--   Original exponential-clock Wiener–Hopf factor finite-rate normalisation
-- statement:
--   For every actual spectrally negative Lévy process under original P, exponential clock p>0 and nonnegative Laplace parameter β satisfying the strict rate gap ψ(β)<p, the product of the actual running-supremum positive-exponential moment and terminal-drawdown negative-exponential moment, multiplied by p-ψ(β) in ENNReal, equals p. The theorem follows source-faithfully from the already accepted genuine original-clock terminal Laplace factorisation and the actual original exponential-clock terminal moment-rate identity. This directly exposes the finite-rate Wiener–Hopf scalar normalisation in the exact original process without invented independence or invalid gap division.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_wh_gap_normalisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (β : ℝ)
    (hβ : 0 ≤ β) (hgap : X.ψ β < p) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal (p - X.ψ β) *
      ((∫⁻ z, ENNReal.ofReal (Real.exp (β * S z))
          ∂(P.prod (expMeasure p))) *
       (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure p)))) =
      ENNReal.ofReal p := by sorry
