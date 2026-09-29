-- Prove2me | solution 1 for mme_schonhage_direct_sum
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:38:33.255431+00:00
-- url     : https://prove2.me/submissions/27a4d9ae-0e43-4e2d-9d2c-08913b074284
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Fin.VecNotation
import Theorems.Thm_mme_degenerates_asymptoticRank_le
import Theorems.Thm_mme_schonhage_degenerates
import Definitions.Def_mme_tensor_rank

open MME


open MME

universe u

/-! # Sketch: `AR(⟨4,1,4⟩ ⊕ ⟨1,9,1⟩) ≤ 17`

Decomposition of `mme_schonhage_direct_sum` into:

  * `mme_schonhage_degenerates`          — the explicit order-2 degeneration witnessing
    border rank `≤ 17` (Schönhage's construction);
  * `mme_degenerates_asymptoticRank_le`  — degeneration (border rank `≤ r`) bounds
    asymptotic rank by `r`.

The sketch packages the order-2 degeneration as a `Degenerates` witness and feeds it to
the border-rank ⇒ asymptotic-rank bound. -/

theorem solution {K : Type u} [Field K] :
    tensorAsymptoticRank (TensorObj.bigAdd ![MMObj K 4 1 4, MMObj K 1 9 1]) ≤ 17 := by
  exact_mod_cast mme_degenerates_asymptoticRank_le ⟨2, mme_schonhage_degenerates⟩
