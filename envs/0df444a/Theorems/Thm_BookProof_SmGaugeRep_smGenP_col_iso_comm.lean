-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_smGenP_col_iso_comm
-- name    : BookProof.SmGaugeRep.smGenP_col_iso_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:56:34.053171+00:00
-- url     : https://prove2.me/theorems/a9c48637-5e97-4df4-a476-d841ac08713c
-- title:
--   `BookProof.SmGaugeRep.smGenP_col_iso_comm` (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.smGenP_col_iso_comm` (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B) = ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.smGenP_col_iso_comm`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.smGenP_col_iso_comm
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.smGenP_col_iso_comm (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B)
      = ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by sorry
