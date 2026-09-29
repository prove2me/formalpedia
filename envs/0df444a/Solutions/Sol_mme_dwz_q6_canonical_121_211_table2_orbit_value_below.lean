-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_211_table2_orbit_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:20:07.842396+00:00
-- url     : https://prove2.me/submissions/3aa793b6-87ce-4399-a7e3-14780cf3c9cd

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_public_cyclic_orbit_product_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_dwz_q6_121_211_componentBase_cube

open MME MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (13 : Fin 15)) :
    HasTauValueAtLeast
      (TensorObj.kron
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 1 1 2))
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 2 1 1))
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 1 2 1))))
      tau (V ^ (3 : ℕ)) := by
  have hV3 : 0 ≤ V ^ (3 : ℕ) := pow_nonneg hV 3
  have hV3lt :
      V ^ (3 : ℕ) <
        4 * Real.rpow 6 (3 * tau) *
          (Real.rpow 6 (3 * tau) + 2) := by
    have hpow := pow_lt_pow_left₀ hVlt hV (by norm_num : (3 : ℕ) ≠ 0)
    rw [mme_dwz_q6_121_211_componentBase_cube tau] at hpow
    exact hpow
  have hraw :
      HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau
        (V ^ (3 : ℕ)) :=
    mme_CW_q6_coupled_raw_cyclic_value_below tau htau
      (V ^ (3 : ℕ)) hV3 hV3lt
  have horbit :
      TensorObj.Restrict
        (cyclicSymmetrization (coupledObj K 6))
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 1 1 2))
          (TensorObj.kron
            ((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 2 1 1))
            ((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 1 2 1)))) := by
    rw [cyclicSymmetrization_eq_public_perm]
    exact mme_CW_public_cyclic_orbit_product_restrict (K := K) 6
      (mme_CW_square_canonical_coupled112_restrict (K := K) 6)
      (mme_CW_square_canonical_coupled211_restrict (K := K) 6)
      (mme_CW_square_canonical_coupled121_restrict (K := K) 6)
  exact mme_HasTauValueAtLeast_mono_restrict horbit hraw
