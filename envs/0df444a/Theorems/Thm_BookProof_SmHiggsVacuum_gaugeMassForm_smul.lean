-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_gaugeMassForm_smul
-- name    : BookProof.SmHiggsVacuum.gaugeMassForm_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:14:23.626419+00:00
-- url     : https://prove2.me/theorems/5772608d-1cd0-4850-b1d5-9868f87ff6e6
-- title:
--   `BookProof.SmHiggsVacuum.gaugeMassForm_smul` (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) (c : ℝ) : gaugeMassForm (fun i => c • X i) u = c ^ 2 * gaugeMassForm X u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.gaugeMassForm_smul` (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) (c : ℝ) : gaugeMassForm (fun i => c • X i) u = c ^ 2 * gaugeMassForm X u
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.gaugeMassForm_smul`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.gaugeMassForm_smul
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.gaugeMassForm_smul (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) (c : ℝ) :
    gaugeMassForm (fun i => c • X i) u = c ^ 2 * gaugeMassForm X u := by sorry
