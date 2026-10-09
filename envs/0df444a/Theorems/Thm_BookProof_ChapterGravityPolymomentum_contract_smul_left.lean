-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_contract_smul_left
-- name    : BookProof.ChapterGravityPolymomentum.contract_smul_left
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:50:55.977153+00:00
-- url     : https://prove2.me/theorems/885c5ead-486c-47a3-ba33-d6cb35491787
-- title:
--   `BookProof.ChapterGravityPolymomentum.contract_smul_left` (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : contract (c • A) B = c * contract A B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.contract_smul_left` (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : contract (c • A) B = c * contract A B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.contract_smul_left`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.contract_smul_left
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

theorem BookProof.ChapterGravityPolymomentum.contract_smul_left (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    contract (c • A) B = c * contract A B := by sorry
