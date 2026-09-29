-- Prove2me | solution 1 for mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:35:23.522221+00:00
-- url     : https://prove2.me/submissions/3fe2b082-6018-493e-91a4-8a0247dd582f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_finite_capacity
import Theorems.Thm_mme_CW_q6_primary_profile_capacity_quarter_root

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L Gcount)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) *
            (((side * side * side : ℕ) : ℝ) ^ tau) := by
  have hhash :=
    mme_CW_q6_primary_hash_Ctensor_finite_capacity
      (K := K) tau htau
  have hprofile :=
    mme_CW_q6_primary_profile_capacity_quarter_root tau htau
  filter_upwards [hhash, hprofile] with N hhashN hprofileN
  dsimp only at hhashN hprofileN ⊢
  intro hconditions
  obtain ⟨A, H, hHpos, hHbound, hmacro, hcapacity⟩ :=
    hhashN hconditions
  refine ⟨A, H, hHpos, hHbound, hmacro, ?_⟩
  exact (hprofileN hconditions).trans
    (mul_le_mul_of_nonneg_right hcapacity (by positivity))
