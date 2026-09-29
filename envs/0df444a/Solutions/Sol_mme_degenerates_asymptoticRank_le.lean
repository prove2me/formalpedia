-- Prove2me | solution 1 for mme_degenerates_asymptoticRank_le
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:40:28.68964+00:00
-- url     : https://prove2.me/submissions/36099bc9-cced-41ea-a18a-73f1a71182bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_asymptoticRank_le_of_pow_rank_bound
import Theorems.Thm_mme_degenerate_pow_rank_bound
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank

open MME


open MME

universe u

/-! # Sketch: degeneration ⇒ asymptotic rank ≤ r

Decomposition of `mme_degenerates_asymptoticRank_le` into:

  * `mme_degenerate_pow_rank_bound`            — border rank `≤ r` gives subexponential
    rank growth `rank(X^⊗(n+1)) ≤ r^(n+1)·C(n+1)` (the algebraic content);
  * `mme_asymptoticRank_le_of_pow_rank_bound`  — such a bound forces
    `tensorAsymptoticRank X ≤ r` (the analytic core, already proved).

The sketch extracts the subexponential factor and feeds it to the analytic bound. -/

theorem solution {K : Type u} [Field K] {d : ℕ}
    {X : TensorObj K d} {r : ℕ}
    (h : Degenerates X (TensorObj.diagObj K d r)) :
    tensorAsymptoticRank X ≤ r := by
  obtain ⟨C, hC1, hlim, hb⟩ := mme_degenerate_pow_rank_bound h
  exact mme_asymptoticRank_le_of_pow_rank_bound X r C hC1 hlim hb
