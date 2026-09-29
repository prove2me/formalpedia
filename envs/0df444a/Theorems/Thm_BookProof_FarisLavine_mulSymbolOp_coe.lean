-- Prove2me | Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_coe
-- name    : BookProof.FarisLavine.mulSymbolOp_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:43:26.199348+00:00
-- url     : https://prove2.me/theorems/cccf1293-a06c-4db8-a757-a43ea192b652
-- title:
--   The Lean 4 theorem `mulSymbolOp_coe` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulSymbolOp_coe` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.mulSymbolOp_coe
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.mulSymbolOp_coe (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|)
    (f : mulSymbolDomain lam) :
    ((mulSymbolOp lam s hs f : L2Nat) : ℕ → ℂ) = mulSymbolFun s ((f : L2Nat) : ℕ → ℂ) := by sorry
