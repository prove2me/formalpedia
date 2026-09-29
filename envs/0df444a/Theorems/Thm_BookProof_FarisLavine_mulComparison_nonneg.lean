-- Prove2me | Theorems.Thm_BookProof_FarisLavine_mulComparison_nonneg
-- name    : BookProof.FarisLavine.mulComparison_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:22:49.327916+00:00
-- url     : https://prove2.me/theorems/dc136fbd-e0e8-4951-bbb8-978fb4508479
-- title:
--   The Lean 4 theorem `mulComparison_nonneg` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulComparison_nonneg` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.mulComparison_nonneg
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.mulComparison_nonneg (lam : ℕ → ℝ) (x : mulSymbolDomain lam) :
    0 ≤ quadForm (mulComparison lam) x := by sorry
