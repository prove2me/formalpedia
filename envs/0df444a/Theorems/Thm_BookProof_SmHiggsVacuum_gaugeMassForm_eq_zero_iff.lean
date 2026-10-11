-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_gaugeMassForm_eq_zero_iff
-- name    : BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:41.624988+00:00
-- url     : https://prove2.me/theorems/01ca05a1-444b-498c-94d7-636a22d66720
-- title:
--   `BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff` (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) : gaugeMassForm X u = 0 ↔ ∀ i, (X i).mulVec u = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff` (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) : gaugeMassForm X u = 0 ↔ ∀ i, (X i).mulVec u = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) :
    gaugeMassForm X u = 0 ↔ ∀ i, (X i).mulVec u = 0 := by sorry
