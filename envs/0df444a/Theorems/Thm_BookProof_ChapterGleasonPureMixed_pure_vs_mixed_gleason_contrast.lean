-- Prove2me | Theorems.Thm_BookProof_ChapterGleasonPureMixed_pure_vs_mixed_gleason_contrast
-- name    : BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:55:53.126024+00:00
-- url     : https://prove2.me/theorems/19e5a91d-ae08-4113-be52-59551bd1fb72
-- title:
--   `BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast` : (¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsPureState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2) ∧ (∃ ρ : Matrix (Fin 2) (Fin 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGleasonPureMixed`.
--
--   `BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast` : (¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsPureState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2) ∧ (∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsMixedState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast`.

-- Generated from ChapterGleasonPureMixed.lean — theorem BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterB4
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.ChapterB4
open BookProof.BRSTNilpotent
open BookProof.ChapterGleasonPureMixed


open scoped BigOperators
open Matrix

theorem BookProof.ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast :
    (¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsPureState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2) ∧
    (∃ ρ : Matrix (Fin 2) (Fin 2) ℝ, IsMixedState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2) := by sorry
