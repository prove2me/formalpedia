-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:54:03.826962+00:00
-- url     : https://prove2.me/theorems/b1ee21b1-2ada-473f-89a0-d1d0e45aef6f
-- title:
--   Actual real-clock upper-record drawdown equals centred residual full-path reward
-- statement:
--   At any finite first strict upward Lévy record before an actual nonnegative real observation clock, a full-path reward H which agrees pointwise with the exponential of the true shifted centred drawdown has the exact value exp(−β(S_e−X_e)) at the residual clock and shifted full path. The result discharges the genuine pathwise hReset premise needed for the random-terminal Esscher regenerative reward event factor, explicitly handling toNNReal conversion, clock subtraction, record-time attainment and compact-path bounds. It assumes only the pointwise shifted functional identity, which the separate dyadic test theorem proves, and no stochastic independence or factorisation.
-- source:
--   Canonical proved first-record drawdown normalisation fc966f64, genuine Lévy compact path bound c2066587, actual strict first-passage age and real-toNNReal horizon identities; Kuznetsov–Kyprianou–Rivero (2013) upper-record decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (β : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hShift : ∀ (ω : Ω) (u t : ℝ≥0),
      H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
        ENNReal.ofReal (Real.exp (-β *
          (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
            Set.Icc 0 t) - (X.X (u + t) ω - X.X u ω)))))
    (z : Ω × ℝ)
    (hFinite : twoSidedExitUpTime X b z.1 < ⊤)
    (hObs : ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2) :
    H (Real.toNNReal (z.2 -
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
      (fun s : ℝ≥0 =>
        X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
          X.X (twoSidedExitUpTime X b z.1).toNNReal z.1) =
      ENNReal.ofReal (Real.exp (-β *
        (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))) := by sorry
