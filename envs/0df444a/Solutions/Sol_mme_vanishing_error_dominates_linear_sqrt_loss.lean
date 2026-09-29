-- Prove2me | solution 1 for mme_vanishing_error_dominates_linear_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:21:25.992861+00:00
-- url     : https://prove2.me/submissions/4fb85d0b-42a8-4754-9fb6-3fded6614471

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology

theorem solution
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (count scale : ℕ) (hcount : 0 < count) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        Real.exp
            (-C * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
          1 - error (count * m) := by
  refine ⟨1, zero_le_one, ?_⟩
  -- `count * m → ∞`, so the error along the subsequence tends to `0`.
  have hcm : Tendsto (fun m : ℕ => count * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => hm.trans (Nat.le_mul_of_pos_left m hcount)⟩
  have hpos : (0 : ℝ) < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at this
    linarith
  have hev : ∀ᶠ m : ℕ in atTop, error (count * m) < 1 - Real.exp (-1) :=
    (herror.comp hcm).eventually (gt_mem_nhds hpos)
  filter_upwards [hev] with m hm
  -- `√(scale·m + 1) ≥ 1`, so the exponential is at most `e⁻¹`.
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (((scale * m + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hexp : Real.exp (-1 * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith
