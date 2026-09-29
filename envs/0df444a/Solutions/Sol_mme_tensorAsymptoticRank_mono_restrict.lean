-- Prove2me | solution 1 for mme_tensorAsymptoticRank_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:26:34.306621+00:00
-- url     : https://prove2.me/submissions/4ac75fcb-450f-470b-ab28-b3d25c9f1127

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality

open MME

universe u

theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    tensorAsymptoticRank X ≤ tensorAsymptoticRank Y := by
  let hd : (1 : ℕ) < 3 := by norm_num
  let P := TensorQ.tensorStrassen K 3 hd
  rw [TensorQ.tensorAsymptoticRank_eq hd X,
    TensorQ.tensorAsymptoticRank_eq hd Y,
    mme_strassen_duality, mme_strassen_duality]
  apply ciSup_le
  intro phi
  have hXY : P.le (TensorQ.toQ X) (TensorQ.toQ Y) := by
    change TensorQ.le (TensorQ.toQ X) (TensorQ.toQ Y)
    exact h
  exact (phi.monotone' hXY).trans
    (le_ciSup (StrassenPreorder.spectrum_eval_bddAbove P (TensorQ.toQ Y)) phi)
