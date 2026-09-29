-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_hasDerivAt_smul_of_bounded
-- name    : BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:57:08.408065+00:00
-- url     : https://prove2.me/theorems/93bdf171-ede4-4406-9366-88ecb8dbdef8
-- title:
--   The Lean 4 theorem `eq_zero_of_hasDerivAt_smul_of_bounded` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_hasDerivAt_smul_of_bounded` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded (g : ℝ → ℂ) (s C : ℝ) (hs : s * s = 1)
    (hgd : ∀ t : ℝ, HasDerivAt g ((s : ℂ) * g t) t) (hb : ∀ t : ℝ, ‖g t‖ ≤ C) : g 0 = 0 := by sorry
