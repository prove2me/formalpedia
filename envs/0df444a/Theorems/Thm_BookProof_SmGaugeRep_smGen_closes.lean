-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_smGen_closes
-- name    : BookProof.SmGaugeRep.smGen_closes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:56:52.460986+00:00
-- url     : https://prove2.me/theorems/e4793947-f1c0-4200-b73d-a6f22b8cce5f
-- title:
--   `BookProof.SmGaugeRep.smGen_closes` (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) : ClosesWithStructureConstants (smGen S3 y) (smStruct f3)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.smGen_closes` (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) : ClosesWithStructureConstants (smGen S3 y) (smStruct f3)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.smGen_closes`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.smGen_closes
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost
open BookProof.YangMillsSU3
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.smGen_closes (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) :
    ClosesWithStructureConstants (smGen S3 y) (smStruct f3) := by sorry
