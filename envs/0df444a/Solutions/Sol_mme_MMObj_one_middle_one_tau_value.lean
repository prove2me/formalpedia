-- Prove2me | solution 1 for mme_MMObj_one_middle_one_tau_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:17:32.210919+00:00
-- url     : https://prove2.me/submissions/93364616-1a7f-416d-b886-64fabcc53a8b

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_kronFin_MMObj_iso

open Filter BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

universe u

private theorem kronFin_const_MM_one_middle
    {K : Type u} [Field K] (r N : ℕ) :
    TensorObj.kronFin N (fun _ ↦ MMObj K 1 r 1) =
      (MMObj K 1 r 1).kronPow N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change TensorObj.kron (MMObj K 1 r 1)
          (TensorObj.kronFin N (fun _ ↦ MMObj K 1 r 1)) =
        TensorObj.kron (MMObj K 1 r 1) ((MMObj K 1 r 1).kronPow N)
      rw [ih]

theorem solution
    {K : Type u} [Field K]
    (r : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (MMObj K 1 r 1) tau (Real.rpow r tau) := by
  constructor
  · exact Real.rpow_nonneg (Nat.cast_nonneg r) tau
  · intro epsilon hepsilon
    apply (Filter.Eventually.of_forall (fun N ↦ ?_)).frequently
    refine ⟨1, (fun _ ↦ 1), (fun _ ↦ r ^ N), (fun _ ↦ 1), ?_, ?_⟩
    · change TensorObj.Restrict (MMObj K 1 (r ^ N) 1)
        ((MMObj K 1 r 1).kronPow N)
      rw [← kronFin_const_MM_one_middle (K := K) r N]
      have hiso := mme_kronFin_MMObj_iso (K := K) N
        (fun _ ↦ 1) (fun _ ↦ r) (fun _ ↦ 1)
      simpa using hiso.2
    · simp only [Fin.sum_univ_one]
      have hbase0 : 0 ≤ Real.rpow r tau :=
        Real.rpow_nonneg (Nat.cast_nonneg r) tau
      have hone : 1 - epsilon ≤ (1 : ℝ) := by linarith
      calc
        Real.rpow r tau ^ N * (1 - epsilon)
            ≤ Real.rpow r tau ^ N * 1 :=
          mul_le_mul_of_nonneg_left hone (pow_nonneg hbase0 N)
        _ = Real.rpow (r ^ N) tau := by
          simp only [mul_one]
          calc
            Real.rpow r tau ^ N = Real.rpow r (tau * (N : ℝ)) := by
              exact (Real.rpow_mul_natCast (Nat.cast_nonneg r) tau N).symm
            _ = Real.rpow r ((N : ℝ) * tau) := by ring_nf
            _ = Real.rpow ((r : ℝ) ^ N) tau := by
              exact Real.rpow_natCast_mul (Nat.cast_nonneg r) N tau
            _ = Real.rpow (r ^ N) tau := by norm_cast
        _ = (((1 * r ^ N * 1 : ℕ) : ℝ) ^ tau) := by
          norm_num
