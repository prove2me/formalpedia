-- Prove2me | Theorems.Thm_BookProof_ChapterA4f_zeroMomentum_symbol
-- name    : BookProof.ChapterA4f.zeroMomentum_symbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:42:19.880655+00:00
-- url     : https://prove2.me/theorems/f639b1ba-a157-496b-8451-8a9ead2e9c73
-- title:
--   `BookProof.ChapterA4f.zeroMomentum_symbol` (m₁ m₂ : ℝ) : energySymbolR (fun _ => 0) m₁ m₂ * energySymbolR (fun _ => 0) m₁ m₂ = (-(m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4f`.
--
--   `BookProof.ChapterA4f.zeroMomentum_symbol` (m₁ m₂ : ℝ) : energySymbolR (fun _ => 0) m₁ m₂ * energySymbolR (fun _ => 0) m₁ m₂ = (-(m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4f.zeroMomentum_symbol`.

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.zeroMomentum_symbol
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4f.zeroMomentum_symbol (m₁ m₂ : ℝ) :
    energySymbolR (fun _ => 0) m₁ m₂ * energySymbolR (fun _ => 0) m₁ m₂
      = (-(m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by sorry
