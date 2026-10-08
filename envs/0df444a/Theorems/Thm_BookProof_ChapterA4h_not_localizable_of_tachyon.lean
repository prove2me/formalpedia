-- Prove2me | Theorems.Thm_BookProof_ChapterA4h_not_localizable_of_tachyon
-- name    : BookProof.ChapterA4h.not_localizable_of_tachyon
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:53.677986+00:00
-- url     : https://prove2.me/theorems/01eeb9a3-ad25-4908-b87f-4fc92d2d42bb
-- title:
--   `BookProof.ChapterA4h.not_localizable_of_tachyon` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 < m₁ ^ 2 + m₂ ^ 2) : ¬ Localizable p m₁ m₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4h`.
--
--   `BookProof.ChapterA4h.not_localizable_of_tachyon` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 < m₁ ^ 2 + m₂ ^ 2) : ¬ Localizable p m₁ m₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4h.not_localizable_of_tachyon`.

-- Generated from ChapterA4h.lean — theorem BookProof.ChapterA4h.not_localizable_of_tachyon
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4h
open BookProof.ChapterA4h


open Matrix


open BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5

theorem BookProof.ChapterA4h.not_localizable_of_tachyon (p : Fin 3 → ℝ) (m₁ m₂ : ℝ)
    (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 < m₁ ^ 2 + m₂ ^ 2) :
    ¬ Localizable p m₁ m₂ := by sorry
