-- Prove2me | solution 1 for mme_CW_square_laser_2376_profile_rate_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:58:26.201443+00:00
-- url     : https://prove2.me/submissions/6f2a5594-5409-4d4b-9644-927928329c30

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_CW_square_2376_profile_hash_pruned_cores
import Theorems.Thm_mme_CW_2376_profile_core_substitution
import Theorems.Thm_mme_CW_2376_auxiliary_profile_factorization

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc) :
    ∃ rate : ℕ → ℝ,
      Tendsto rate atTop (nhds 0) ∧
      (∀ m, 0 ≤ rate m) ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (delta : ℝ), 0 < delta → delta < 1 →
        ∀ (kc : ℕ) (xc yc zc : Fin kc → ℕ),
          TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i)))
              ((cyclicSymmetrization (coupledObj K 6)).kronPow m) →
          Vc ^ m * (1 - delta) ≤
            ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau) →
          ∃ (k : ℕ) (x y z : Fin k → ℕ),
            TensorObj.Restrict
                (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
                ((CWObj K 6).kronPow (6000000 * m)) ∧
            (auxiliaryRHSWithCoupled 6 tau
                cw2376_a cw2376_b cw2376_c cw2376_d Vc *
              Real.exp (-(rate m))) ^ (3000000 * m) *
                (1 - delta) ^ (616627 : ℕ) ≤
              ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨rate, hrate, hrate_nonneg, hhash⟩ :=
    mme_CW_square_2376_profile_hash_pruned_cores (K := K)
  refine ⟨rate, hrate, hrate_nonneg, ?_⟩
  filter_upwards [hhash] with m hm
  intro delta hdelta_pos hdelta_lt kc xc yc zc hc_restrict hc_weight
  obtain ⟨s, hs_restrict, hs_count⟩ := hm
  obtain ⟨k, x, y, z, hcore_restrict, hweight⟩ :=
    mme_CW_2376_profile_core_substitution
      (K := K) tau htau Vc hVc_nonneg m s delta hdelta_pos hdelta_lt
      kc xc yc zc hc_restrict hc_weight
  refine ⟨k, x, y, z,
    TensorObj.Restrict.trans hcore_restrict hs_restrict, ?_⟩
  let E : ℝ := Real.exp (-(rate m))
  let C : ℝ := cw2376ProfileCountBase
  let P : ℝ := cw2376ProfileNumeratorBase tau Vc
  let D : ℝ := (1 - delta) ^ (616627 : ℕ)
  have hP : 0 ≤ P := by
    dsimp [P, cw2376ProfileNumeratorBase]
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 12) _)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 38) _))
      (Real.rpow_nonneg hVc_nonneg _)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact pow_nonneg (sub_nonneg.mpr hdelta_lt.le) _
  have hs_count' :
      (C * E) ^ (3000000 * m) ≤ (s : ℝ) := by
    simpa [C, E] using hs_count
  have hfactor : 0 ≤ P ^ (3000000 * m) * D :=
    mul_nonneg (pow_nonneg hP _) hD
  have hmul :
      (C * E) ^ (3000000 * m) * P ^ (3000000 * m) * D ≤
        (s : ℝ) * P ^ (3000000 * m) * D := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right hs_count' hfactor)
  calc
    (auxiliaryRHSWithCoupled 6 tau
          cw2376_a cw2376_b cw2376_c cw2376_d Vc *
        Real.exp (-(rate m))) ^ (3000000 * m) *
          (1 - delta) ^ (616627 : ℕ)
        = (C * E) ^ (3000000 * m) * P ^ (3000000 * m) * D := by
          rw [mme_CW_2376_auxiliary_profile_factorization]
          simp only [C, E, P, D]
          rw [← mul_pow]
          congr 2
          ring
    _ ≤ (s : ℝ) * P ^ (3000000 * m) * D := hmul
    _ ≤ ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
      simpa [P, D] using hweight
