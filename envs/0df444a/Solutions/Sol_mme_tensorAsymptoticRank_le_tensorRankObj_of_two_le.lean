-- Prove2me | solution 1 for mme_tensorAsymptoticRank_le_tensorRankObj_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:29:28.940559+00:00
-- url     : https://prove2.me/submissions/8e5f799e-a946-4517-a2bd-a1a3f8105162

import Definitions.Def_mme_rank_bridge

open MME

universe u

/-! The concrete asymptotic rank is at most the one-shot tensor rank. -/

theorem solution {K : Type u} [Field K] {d : ℕ}
    (hd : 1 < d) (X : TensorObj K d) :
    tensorAsymptoticRank X ≤ tensorRankObj X := by
  rw [TensorQ.tensorAsymptoticRank_eq hd,
    ← TensorQ.rank_tensorStrassen_toQ hd]
  let P := TensorQ.tensorStrassen K d hd
  let a := TensorQ.toQ X
  have hi :
      (⨅ n : ℕ,
        (StrassenPreorder.rank P (a ^ (n + 1)) : ℝ) ^
          ((1 : ℝ) / (n + 1))) ≤
        (StrassenPreorder.rank P a : ℝ) := by
    have hbdd : BddBelow (Set.range (fun n : ℕ =>
        (StrassenPreorder.rank P (a ^ (n + 1)) : ℝ) ^
          ((1 : ℝ) / (n + 1)))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      positivity
    refine ciInf_le_of_le hbdd (0 : ℕ) ?_
    norm_num only [zero_add, Nat.cast_zero, Nat.cast_one, one_div,
      pow_one]
    exact (Real.rpow_one _).le
  simpa only [StrassenPreorder.asymptoticRank] using hi
