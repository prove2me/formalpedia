-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_norm_crossB_le
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:23:14.699907+00:00
-- url     : https://prove2.me/theorems/d7932935-cf75-4cd5-b2b4-aa19864a624d
-- title:
--   (X Y : ι → ℂ) (β : ι) : ‖S.crossB X Y β‖ ≤ S.maj.ampSeq X (S.shift β) * ‖Y β‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le (X Y : ι → ℂ) (β : ι) :
    ‖S.crossB X Y β‖ ≤ S.maj.ampSeq X (S.shift β) * ‖Y β‖ := by sorry
