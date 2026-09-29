-- Prove2me | solution 1 for mme_CW_square_asymptoticRank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:33:39.822362+00:00
-- url     : https://prove2.me/submissions/6c3609bd-fa96-4b1a-a561-a0c13535260d

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality
import Theorems.Thm_mme_CW_border_rank_le
import Theorems.Thm_mme_degenerates_asymptoticRank_le

open MME

universe u

private lemma tensorAsymptoticRank_nonneg
    {K : Type u} [Field K] {d : ℕ} (T : TensorObj K d) :
    0 ≤ tensorAsymptoticRank T := by
  unfold tensorAsymptoticRank
  change (0 : ℝ) ≤ ⨅ n : ℕ,
    (tensorRankObj (T.kronPow (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1))
  apply le_ciInf
  intro n
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem solution {K : Type u} [Field K] (q : ℕ) :
    tensorAsymptoticRank
        (TensorObj.kron (CWObj K q) (CWObj K q)) ≤
      ((q : ℝ) + 2) ^ (2 : ℕ) := by
  let X := CWObj K q
  have hX : tensorAsymptoticRank X ≤ (q + 2 : ℕ) :=
    mme_degenerates_asymptoticRank_le (mme_CW_border_rank_le q)
  have hX' : tensorAsymptoticRank X ≤ (q : ℝ) + 2 := by
    exact_mod_cast hX
  rw [TensorQ.tensorAsymptoticRank_eq (by norm_num : 1 < 3),
    TensorQ.toQ_kron]
  rw [show TensorQ.toQ X * TensorQ.toQ X = (TensorQ.toQ X) ^ (2 : ℕ) by
    ring]
  rw [StrassenPreorder.asymptoticRank_pow _ _ 2 (by norm_num)]
  rw [← TensorQ.tensorAsymptoticRank_eq (by norm_num : 1 < 3)]
  exact pow_le_pow_left₀ (tensorAsymptoticRank_nonneg X) hX' 2
