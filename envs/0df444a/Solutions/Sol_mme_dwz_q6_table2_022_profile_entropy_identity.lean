-- Prove2me | solution 1 for mme_dwz_q6_table2_022_profile_entropy_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:23:44.945411+00:00
-- url     : https://prove2.me/submissions/7b0fde7f-d5e5-4e54-8f63-76cbcc409e6f

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

theorem solution :
    let a : ℝ := splitA
    let g : ℝ := 1 - 2 * a
    let profile : Fin 3 → ℝ := ![a, g, a]
    Real.exp (Real.log 2 * mme_modern_entropyBits profile) =
      1 / (Real.rpow a (2 * a) * Real.rpow g g) := by
  dsimp only
  have ha : 0 < splitA := by norm_num [splitA]
  have hg : 0 < 1 - 2 * splitA := by norm_num [splitA]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hrhs :
      0 < 1 /
        (Real.rpow splitA (2 * splitA) *
          Real.rpow (1 - 2 * splitA) (1 - 2 * splitA)) := by
    exact one_div_pos.mpr <| mul_pos
      (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hg _)
  apply Real.log_injOn_pos (Real.exp_pos _) hrhs
  rw [Real.log_exp]
  unfold mme_modern_entropyBits
  rw [mul_div_cancel₀ _ hlog2]
  have hsum :
      (∑ i : Fin 3,
        Real.negMulLog (![splitA, 1 - 2 * splitA, splitA] i)) =
        Real.negMulLog splitA +
          Real.negMulLog (1 - 2 * splitA) +
          Real.negMulLog splitA := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  unfold Real.negMulLog
  rw [one_div, Real.log_inv]
  rw [Real.log_mul
    (x := Real.rpow splitA (2 * splitA))
    (y := Real.rpow (1 - 2 * splitA) (1 - 2 * splitA))
    (Real.rpow_pos_of_pos ha _).ne'
    (Real.rpow_pos_of_pos hg _).ne']
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
  rw [Real.log_rpow ha (2 * splitA)]
  rw [Real.log_rpow hg (1 - 2 * splitA)]
  ring
