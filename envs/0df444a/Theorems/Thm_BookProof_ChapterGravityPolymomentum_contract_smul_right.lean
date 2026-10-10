-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_contract_smul_right
-- name    : BookProof.ChapterGravityPolymomentum.contract_smul_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:48:14.186609+00:00
-- url     : https://prove2.me/theorems/eb30244d-080b-4ef8-ab95-fbcd4818d5ff
-- title:
--   `BookProof.ChapterGravityPolymomentum.contract_smul_right` (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : contract A (c • B) = c * contract A B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.contract_smul_right` (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : contract A (c • B) = c * contract A B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.contract_smul_right`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.contract_smul_right
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

theorem BookProof.ChapterGravityPolymomentum.contract_smul_right (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    contract A (c • B) = c * contract A B := by sorry
