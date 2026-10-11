-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_pos_of_ne
-- name    : BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:42.561975+00:00
-- url     : https://prove2.me/theorems/0d93b0f9-7fbb-484d-8db3-662357691920
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne` {beta : ℝ} {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) : 0 < varScore beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne` {beta : ℝ} {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) : 0 < varScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne {beta : ℝ} {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) :
    0 < varScore beta s := by sorry
