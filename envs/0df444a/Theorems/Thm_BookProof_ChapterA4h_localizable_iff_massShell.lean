-- Prove2me | Theorems.Thm_BookProof_ChapterA4h_localizable_iff_massShell
-- name    : BookProof.ChapterA4h.localizable_iff_massShell
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:31.589919+00:00
-- url     : https://prove2.me/theorems/8fa6b6a6-22d1-4bf7-85d6-d36462ea6dc5
-- title:
--   `BookProof.ChapterA4h.localizable_iff_massShell` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : Localizable p m₁ m₂ ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = m₁ ^ 2 + m₂ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4h`.
--
--   `BookProof.ChapterA4h.localizable_iff_massShell` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : Localizable p m₁ m₂ ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = m₁ ^ 2 + m₂ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4h.localizable_iff_massShell`.

-- Generated from ChapterA4h.lean — theorem BookProof.ChapterA4h.localizable_iff_massShell
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA4f
import Mathlib
import Definitions.Def_ChapterA4h
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4h


open Matrix


open BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5

theorem BookProof.ChapterA4h.localizable_iff_massShell (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    Localizable p m₁ m₂ ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = m₁ ^ 2 + m₂ ^ 2 := by sorry
