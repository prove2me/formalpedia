-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_norm_crossA_le
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:22:29.77756+00:00
-- url     : https://prove2.me/theorems/840c1e84-e3e4-4b95-918f-142ba3959713
-- title:
--   (X Y : ι → ℂ) (β : ι) : ‖S.crossA X Y β‖ ≤ S.maj.ampSeq X β * ‖Y (S.shift β)‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le (X Y : ι → ℂ) (β : ι) :
    ‖S.crossA X Y β‖ ≤ S.maj.ampSeq X β * ‖Y (S.shift β)‖ := by sorry
