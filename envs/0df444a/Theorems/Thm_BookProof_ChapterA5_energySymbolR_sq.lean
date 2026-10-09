-- Prove2me | Theorems.Thm_BookProof_ChapterA5_energySymbolR_sq
-- name    : BookProof.ChapterA5.energySymbolR_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:15:52.083405+00:00
-- url     : https://prove2.me/theorems/26de2a1e-3edc-47cd-9f73-be2131d867bf
-- title:
--   `BookProof.ChapterA5.energySymbolR_sq` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA5`.
--
--   `BookProof.ChapterA5.energySymbolR_sq` (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂ = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA5.energySymbolR_sq`.

-- Generated from ChapterA5.lean — theorem BookProof.ChapterA5.energySymbolR_sq
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA5.energySymbolR_sq (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) •
          (1 : Matrix (Fin 4) (Fin 4) ℝ) := by sorry
