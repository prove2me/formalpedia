-- Prove2me | Theorems.Thm_BookProof_ChapterA5_energySymbolZ_sq
-- name    : BookProof.ChapterA5.energySymbolZ_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:16:14.779999+00:00
-- url     : https://prove2.me/theorems/9d8c36c2-8ebc-4c70-a44c-798df4884ddb
-- title:
--   `BookProof.ChapterA5.energySymbolZ_sq` (p : Fin 3 → ℤ) (m₁ m₂ : ℤ) : energySymbolZ p m₁ m₂ * energySymbolZ p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA5`.
--
--   `BookProof.ChapterA5.energySymbolZ_sq` (p : Fin 3 → ℤ) (m₁ m₂ : ℤ) : energySymbolZ p m₁ m₂ * energySymbolZ p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA5.energySymbolZ_sq`.

-- Generated from ChapterA5.lean — theorem BookProof.ChapterA5.energySymbolZ_sq
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA5.energySymbolZ_sq (p : Fin 3 → ℤ) (m₁ m₂ : ℤ) :
    energySymbolZ p m₁ m₂ * energySymbolZ p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) •
          (1 : Matrix (Fin 4) (Fin 4) ℤ) := by sorry
