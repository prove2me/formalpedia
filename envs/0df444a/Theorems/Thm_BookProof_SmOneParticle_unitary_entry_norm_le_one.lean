-- Prove2me | Theorems.Thm_BookProof_SmOneParticle_unitary_entry_norm_le_one
-- name    : BookProof.SmOneParticle.unitary_entry_norm_le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:14:56.191986+00:00
-- url     : https://prove2.me/theorems/1b551932-f54b-4a29-b32b-d65ac5945825
-- title:
--   `BookProof.SmOneParticle.unitary_entry_norm_le_one` (hV : IsMixing V) (i j : Fin 3) : ‖V i j‖ ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOneParticle`.
--
--   `BookProof.SmOneParticle.unitary_entry_norm_le_one` (hV : IsMixing V) (i j : Fin 3) : ‖V i j‖ ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.SmOneParticle.unitary_entry_norm_le_one`.

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.unitary_entry_norm_le_one
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

variable {V U : Matrix (Fin 3) (Fin 3) ℂ}

theorem BookProof.SmOneParticle.unitary_entry_norm_le_one (hV : IsMixing V) (i j : Fin 3) : ‖V i j‖ ≤ 1 := by sorry
