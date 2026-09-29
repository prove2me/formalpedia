-- Prove2me | solution 1 for mme_CW_square_laser_value_below_2376_of_coupled_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:21:55.906166+00:00
-- url     : https://prove2.me/submissions/ba0a9ce5-39b4-4493-8e1a-93456a039c26

import Theorems.Thm_mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_kron_self_kronPow_isomorphic

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      ∀ Vc : ℝ, 0 ≤ Vc →
        Vc <
          4 * (6 : ℝ) ^ (3 * tau) *
            ((6 : ℝ) ^ (3 * tau) + 2) →
        HasTauValueAtLeast
          (cyclicSymmetrization (coupledObj K 6)) tau Vc)
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    (hV_lt :
      V < auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V := by
  obtain ⟨Vc, hVc_nonneg, hVc_lt, hVc_value, m, hm, hextract⟩ :=
    mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
      (K := K) tau htau hcoupled V hV_nonneg hV_lt
  let s : ℕ → ℕ := fun n => 3000000 * m n
  have hs : Tendsto s atTop atTop := by
    dsimp [s]
    exact hm.nsmul_atTop (by norm_num)
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V hV_nonneg
    s hs (fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hextract] with n hn
  obtain ⟨hprofile, k, x, y, z, hrestrict, hweight⟩ := hn
  refine ⟨k, x, y, z, ?_, ?_⟩
  · have hiso := mme_kron_self_kronPow_isomorphic
      (CWObj K 6) (3000000 * m n)
    apply TensorObj.Restrict.trans ?_ hiso.2
    simpa only [show 2 * (3000000 * m n) = 6000000 * m n by omega] using
      hrestrict
  · simpa only [s, sub_zero, mul_one] using hweight
