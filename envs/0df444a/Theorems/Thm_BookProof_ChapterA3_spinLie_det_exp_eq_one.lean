-- Prove2me | Theorems.Thm_BookProof_ChapterA3_spinLie_det_exp_eq_one
-- name    : BookProof.ChapterA3.spinLie_det_exp_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:48:12.631983+00:00
-- url     : https://prove2.me/theorems/e1b32870-4a30-4267-a0b6-f3d2addb89e7
-- title:
--   `BookProof.ChapterA3.spinLie_det_exp_eq_one` {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : IsSpinLie G) : (NormedSpace.exp G).det = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.spinLie_det_exp_eq_one` {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : IsSpinLie G) : (NormedSpace.exp G).det = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.spinLie_det_exp_eq_one`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.spinLie_det_exp_eq_one
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.spinLie_det_exp_eq_one {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : IsSpinLie G) :
    (NormedSpace.exp G).det = 1 := by sorry
