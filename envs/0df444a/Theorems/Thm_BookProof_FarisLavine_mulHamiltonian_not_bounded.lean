-- Prove2me | Theorems.Thm_BookProof_FarisLavine_mulHamiltonian_not_bounded
-- name    : BookProof.FarisLavine.mulHamiltonian_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:43:19.547767+00:00
-- url     : https://prove2.me/theorems/3f41c29d-c567-4ae8-951f-3a8cbfe61f61
-- title:
--   The Lean 4 theorem `mulHamiltonian_not_bounded` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulHamiltonian_not_bounded` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.mulHamiltonian_not_bounded
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.mulHamiltonian_not_bounded (lam : ℕ → ℝ) (hlam : ∀ C : ℝ, ∃ n, C < |lam n|) :
    ¬ ∃ C : ℝ, ∀ f : mulSymbolDomain lam, ‖mulHamiltonian lam f‖ ≤ C * ‖(f : L2Nat)‖ := by sorry
