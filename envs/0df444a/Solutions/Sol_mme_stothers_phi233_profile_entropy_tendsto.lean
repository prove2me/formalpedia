-- Prove2me | solution 1 for mme_stothers_phi233_profile_entropy_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:36:43.029363+00:00
-- url     : https://prove2.me/submissions/87485739-d65b-4d55-8cb4-2b91a02f10c6

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.Field

open Filter

set_option autoImplicit false
set_option warningAsError true

/-- The symmetric ten-label entropy of an exact integer `phi_233` profile
converges to the entropy of its limiting real profile.  Continuity at zero is
included through `Real.negMulLog`, so no strict-positivity hypothesis is
needed. -/
theorem solution
    (a b c d : ℝ) (A B C D : ℕ → ℕ)
    (hA : Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    Tendsto
      (fun n : ℕ ↦
        4 * Real.negMulLog ((A n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((B n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((C n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((D n : ℝ) / ((2 * n : ℕ) : ℝ)))
      atTop
      (nhds
        (4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2))) := by
  have hA2 : Tendsto
      (fun n : ℕ ↦ (A n : ℝ) / ((2 * n : ℕ) : ℝ))
      atTop (nhds (a / 2)) := by
    simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using hA.div_const 2
  have hB2 : Tendsto
      (fun n : ℕ ↦ (B n : ℝ) / ((2 * n : ℕ) : ℝ))
      atTop (nhds (b / 2)) := by
    simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using hB.div_const 2
  have hC2 : Tendsto
      (fun n : ℕ ↦ (C n : ℝ) / ((2 * n : ℕ) : ℝ))
      atTop (nhds (c / 2)) := by
    simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using hC.div_const 2
  have hD2 : Tendsto
      (fun n : ℕ ↦ (D n : ℝ) / ((2 * n : ℕ) : ℝ))
      atTop (nhds (d / 2)) := by
    simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using hD.div_const 2
  exact
    ((((Real.continuous_negMulLog.tendsto (a / 2)).comp hA2).const_mul 4).add
      (((Real.continuous_negMulLog.tendsto (b / 2)).comp hB2).const_mul 2)).add
      (((Real.continuous_negMulLog.tendsto (c / 2)).comp hC2).const_mul 2) |>.add
      (((Real.continuous_negMulLog.tendsto (d / 2)).comp hD2).const_mul 2)
