-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_smGenP_hyp_comm
-- name    : BookProof.SmGaugeRep.smGenP_hyp_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:56:36.282333+00:00
-- url     : https://prove2.me/theorems/baf25a6e-c708-4170-af65-6d7f9f200f05
-- title:
--   `BookProof.SmGaugeRep.smGenP_hyp_comm` (y : ℝ) (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) : ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) * M = M * ((y : ℂ)) • (1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.smGenP_hyp_comm` (y : ℝ) (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) : ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) * M = M * ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.smGenP_hyp_comm`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.smGenP_hyp_comm
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.smGenP_hyp_comm (y : ℝ) (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) * M
      = M * ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) := by sorry
