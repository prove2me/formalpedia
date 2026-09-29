-- Prove2me | solution 1 for mme_CW_q6_coupled_hash_survivors_below_raw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:48:20.875621+00:00
-- url     : https://prove2.me/submissions/9fd6acd6-60be-4027-8c54-383b825d8bf9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
import Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_enum_genDim
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ k : ℕ,
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin k => coupledQ6Survivor K L G))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          (k : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  have hcert := mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
    (K := K) tau htau V hV hVlt
  filter_upwards [hcert] with N hcert
  dsimp only at hcert ⊢
  intro hprune
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp,
    hcomponent, hcount⟩ := hcert hprune
  refine ⟨C.card, ?_, hcount⟩
  exact TensorObj.Restrict.trans
    (mme_bigAdd_mono_restrict hcomponent)
    (TensorObj.Restrict.trans
      (mme_independent_blocks_form_direct_sum_restrict_enum_genDim
        grading C σs hmem hinj hdisj hsupp)
      hP)
