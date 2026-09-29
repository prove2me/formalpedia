-- Prove2me | solution 1 for mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:30:09.259288+00:00
-- url     : https://prove2.me/submissions/21b85715-02ca-43a5-86b0-5b34f5b11f5f

import Theorems.Thm_mme_CW_2376_choose_coupled_base_below
import Theorems.Thm_mme_CW_square_laser_2376_tensor_extraction_below

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
    ∃ Vc : ℝ,
      0 ≤ Vc ∧
      Vc <
        4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2) ∧
      HasTauValueAtLeast
        (cyclicSymmetrization (coupledObj K 6)) tau Vc ∧
      ∃ m : ℕ → ℕ,
        Tendsto m atTop atTop ∧
        ∀ᶠ n : ℕ in atTop,
          (3 * (699 * m n) + 6 * (37518 * m n) +
              3 * (307638 * m n) + 3 * (616627 * m n) =
                3000000 * m n ∧
            2 * (699 * m n) + 2 * (37518 * m n) +
                307638 * m n = 384072 * m n ∧
            2 * (37518 * m n) + 2 * (616627 * m n) =
                1308290 * m n ∧
            2 * (307638 * m n) + 616627 * m n =
                1231903 * m n ∧
            2 * (37518 * m n) = 75036 * m n ∧
            699 * m n = 699 * m n ∧
            384072 * m n + 1308290 * m n + 1231903 * m n +
                75036 * m n + 699 * m n = 3000000 * m n) ∧
          ∃ (k : ℕ) (x y z : Fin k → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
              ((CWObj K 6).kronPow (6000000 * m n)) ∧
            V ^ (3000000 * m n) ≤
              ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨Vc, hVc_nonneg, hVc_lt, hV_profile⟩ :=
    mme_CW_2376_choose_coupled_base_below tau V hV_lt
  have hVc_value :=
    hcoupled Vc hVc_nonneg hVc_lt
  obtain ⟨m, hm, hextract⟩ :=
    mme_CW_square_laser_2376_tensor_extraction_below
      (K := K) tau htau Vc hVc_nonneg hVc_value
      V hV_nonneg hV_profile
  exact ⟨Vc, hVc_nonneg, hVc_lt, hVc_value, m, hm, hextract⟩
