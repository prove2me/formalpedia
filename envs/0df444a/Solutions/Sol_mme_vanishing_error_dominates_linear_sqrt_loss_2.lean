-- Prove2me | solution 2 for mme_vanishing_error_dominates_linear_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:23:19.158728+00:00
-- url     : https://prove2.me/submissions/3c60368a-78a9-487c-889c-ca52c6a5594e

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology

set_option autoImplicit false

theorem solution
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (count scale : ℕ) (hcount : 0 < count) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        Real.exp
            (-C * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
          1 - error (count * m) := by
  refine ⟨1, zero_le_one, ?_⟩
  -- the subsequence `error (count * m)` still tends to `0`
  have hmul : Tendsto (fun m : ℕ => count * m) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun m hm =>
      le_trans hm (Nat.le_mul_of_pos_left m hcount)⟩)
  have hcomp : Tendsto (fun m : ℕ => error (count * m)) atTop (nhds 0) :=
    herror.comp hmul
  have hev : ∀ᶠ m : ℕ in atTop, error (count * m) ≤ 1 / 2 :=
    hcomp.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hev] with m hm
  have h1 : (1 : ℝ) ≤ Real.sqrt (((scale * m + 1 : ℕ) : ℝ)) := by
    have : (1 : ℝ) ≤ ((scale * m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (((scale * m + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt this
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hexppos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  calc Real.exp (-1 * Real.sqrt (((scale * m + 1 : ℕ) : ℝ)))
      ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.2
        linarith
    _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
    _ ≤ 1 / 2 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hexp1
    _ ≤ 1 - error (count * m) := by linarith
