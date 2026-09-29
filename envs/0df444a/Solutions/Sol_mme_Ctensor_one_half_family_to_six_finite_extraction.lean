-- Prove2me | solution 1 for mme_Ctensor_one_half_family_to_six_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:58:48.743488+00:00
-- url     : https://prove2.me/submissions/6cbc6eea-f42e-4225-b750-23fdf779e9fc

import Mathlib
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_behrend_log_loss_absorbed_sqrt
import Theorems.Thm_mme_finite_MM_extraction_swap_double_uniform

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (tau : ℝ) (N A H volume : ℕ)
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hH : 0 < H) (hHbound : H ≤ 4 ^ N) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      (((((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            Real.exp (-200 * Real.sqrt (((N + 1 : ℕ) : ℝ)))) ^
          (2 : ℕ)) *
          (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨k, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction stars hH
  let behrend : ℝ := Real.exp
    (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
  let sourceLoss : ℝ := Real.exp
    (-200 * Real.sqrt (((N + 1 : ℕ) : ℝ)))
  let lower : ℝ := (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sourceLoss
  have habsorb : sourceLoss ≤ behrend := by
    simpa only [sourceLoss, behrend] using
      mme_behrend_log_loss_absorbed_sqrt N H hHbound
  have hlower0 : 0 ≤ lower := by
    dsimp only [lower, sourceLoss]
    positivity
  have hlower : lower ≤ (k : ℝ) := by
    calc
      lower = (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 * sourceLoss) := by
        dsimp only [lower]
        norm_num
        ring
      _ ≤ (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 * behrend) := by
        gcongr
      _ ≤ (k : ℝ) := by
        simpa only [behrend] using hcount
  obtain ⟨q, a', b', c', hrestrict', hq, hvolume'⟩ :=
    mme_finite_MM_extraction_swap_double_uniform
      a b c lower hlower0 hlower hrestrict hvolume
  refine ⟨q, a', b', c', hrestrict', ?_⟩
  let weight : ℝ := (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau)
  have hweight0 : 0 ≤ weight := by
    dsimp only [weight]
    positivity
  have hsum :
      (∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau)) =
        (q : ℝ) * weight := by
    dsimp only [weight]
    simp_rw [hvolume']
    simp
  change lower ^ (2 : ℕ) * weight ≤ _
  rw [hsum]
  exact mul_le_mul_of_nonneg_right hq hweight0
