-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_form_closable
-- name    : BookProof.YangMillsFriedrichs.form_closable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:49.186766+00:00
-- url     : https://prove2.me/theorems/68c55f28-2f83-4a4b-8924-e38e04289269
-- title:
--   The Lean 4 theorem `form_closable` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `form_closable` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.form_closable
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.form_closable {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (x : ℕ → D)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, formNormSq H (x p - x q) < ε)
    (hzero : Filter.Tendsto (fun n => ((x n : F))) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => formNormSq H (x n)) Filter.atTop (nhds 0) := by sorry
