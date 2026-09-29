-- Prove2me | solution 1 for mme_stothers_phi233_elementary_component_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:29:53.678474+00:00
-- url     : https://prove2.me/submissions/9a9f6b4d-57af-44ca-a4ea-5ea27b38b9df

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_MMObj_cyclic_tau_value

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 0)) tau
        (MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau) ∧
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 3)) tau
        (MME.StothersFourth.E 6 tau ^ (2 : ℕ)) := by
  have hEH := mme_MMObj_cyclic_tau_value (K := K) 1 38 12 tau
  have hE2 := mme_MMObj_cyclic_tau_value (K := K) 12 12 1 tau
  have heqEH :
      ((((1 * 38 * 12) * (1 * 38 * 12) * (1 * 38 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.E MME.StothersFourth.H
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one]
    rw [show (94818816 : ℝ) = 456 ^ (3 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 456) 3 tau]
    rw [show (456 : ℝ) = 12 * 38 by norm_num]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12)
      (by norm_num : (0 : ℝ) ≤ 38)]
    norm_num
  have heqE2 :
      ((((12 * 12 * 1) * (12 * 12 * 1) * (12 * 12 * 1) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    unfold MME.StothersFourth.E
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one]
    rw [show (2985984 : ℝ) = 12 ^ (6 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 6 tau]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12)
      (3 * tau) 2]
    congr 1
    ring
  constructor
  · simpa only [MME.StothersFourth.Phi233.componentObj,
      Matrix.cons_val_zero] using (heqEH ▸ hEH)
  · simpa only [MME.StothersFourth.Phi233.componentObj,
      Matrix.cons_val_one, Matrix.cons_val_zero] using (heqE2 ▸ hE2)
