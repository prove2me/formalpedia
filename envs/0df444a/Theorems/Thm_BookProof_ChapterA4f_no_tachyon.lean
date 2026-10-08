-- Prove2me | Theorems.Thm_BookProof_ChapterA4f_no_tachyon
-- name    : BookProof.ChapterA4f.no_tachyon
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:42:44.735181+00:00
-- url     : https://prove2.me/theorems/9b074710-e468-4ce0-80e6-1a43f38ca671
-- title:
--   `BookProof.ChapterA4f.no_tachyon` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) •...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4f`.
--
--   `BookProof.ChapterA4f.no_tachyon` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4f.no_tachyon`.

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.no_tachyon
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4f.no_tachyon (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) •
          (1 : Matrix (Fin 4) (Fin 4) ℝ) := by sorry
