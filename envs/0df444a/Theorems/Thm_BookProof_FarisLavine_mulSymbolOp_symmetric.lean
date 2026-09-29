-- Prove2me | Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_symmetric
-- name    : BookProof.FarisLavine.mulSymbolOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:22:05.997911+00:00
-- url     : https://prove2.me/theorems/40aa292c-3bb7-42a9-8793-3d7966c42c4e
-- title:
--   The Lean 4 theorem `mulSymbolOp_symmetric` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulSymbolOp_symmetric` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.mulSymbolOp_symmetric
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.mulSymbolOp_symmetric (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|) :
    SymmetricOn (mulSymbolDomain lam) (mulSymbolOp lam s hs) := by sorry
