-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_memLp_one_div_succ
-- name    : BookProof.YangMillsFriedrichsLimit.memLp_one_div_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:25.308001+00:00
-- url     : https://prove2.me/theorems/cebdb547-505b-40d3-9917-1180705aad45
-- title:
--   The Lean 4 theorem `memℓp_one_div_succ` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `memℓp_one_div_succ` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.memℓp_one_div_succ
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit



open BookProof.FarisLavine BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.memLp_one_div_succ : Memℓp (fun n : ℕ => (1 / (n + 1) : ℂ)) 2 := by sorry
