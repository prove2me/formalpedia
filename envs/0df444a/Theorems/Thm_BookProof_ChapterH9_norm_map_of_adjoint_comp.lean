-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_map_of_adjoint_comp
-- name    : BookProof.ChapterH9.norm_map_of_adjoint_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:38:59.614604+00:00
-- url     : https://prove2.me/theorems/8efb234e-2638-4afb-ab24-de43706e2192
-- title:
--   The Lean 4 theorem `norm_map_of_adjoint_comp` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_map_of_adjoint_comp` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_map_of_adjoint_comp
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.norm_map_of_adjoint_comp {V : F →L[ℂ] E}
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (x : F) : ‖V x‖ = ‖x‖ := by sorry
