-- Prove2me | Theorems.Thm_BookProof_ChapterBoseEinstein_exp_sub_one_pos
-- name    : BookProof.ChapterBoseEinstein.exp_sub_one_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:06:08.999004+00:00
-- url     : https://prove2.me/theorems/bd045c19-6fdb-40f8-a563-4fd43f88408e
-- title:
--   `BookProof.ChapterBoseEinstein.exp_sub_one_pos` (hx : 0 < x) : 0 < Real.exp x - 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBoseEinstein`.
--
--   `BookProof.ChapterBoseEinstein.exp_sub_one_pos` (hx : 0 < x) : 0 < Real.exp x - 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBoseEinstein.exp_sub_one_pos`.

-- Generated from ChapterBoseEinstein.lean — theorem BookProof.ChapterBoseEinstein.exp_sub_one_pos
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterBoseEinstein


noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

theorem BookProof.ChapterBoseEinstein.exp_sub_one_pos (hx : 0 < x) : 0 < Real.exp x - 1 := by sorry
