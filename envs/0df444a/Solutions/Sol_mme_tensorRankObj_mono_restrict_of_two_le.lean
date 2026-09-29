-- Prove2me | solution 1 for mme_tensorRankObj_mono_restrict_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:29:29.744847+00:00
-- url     : https://prove2.me/submissions/ca66416d-2c2a-4dbd-b20e-b67ffc7f80a0

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_spectrum

open MME

universe u


theorem solution {K : Type u} [Field K] {d : ℕ}
    (hd : 1 < d) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y) :
    tensorRankObj X ≤ tensorRankObj Y := by
  rw [← TensorQ.rank_tensorStrassen_toQ hd,
    ← TensorQ.rank_tensorStrassen_toQ hd]
  apply StrassenPreorder.rank_monotone
  exact (TensorQ.le_toQ X Y).2 h
