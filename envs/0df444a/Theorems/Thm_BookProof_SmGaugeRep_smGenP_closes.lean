-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_smGenP_closes
-- name    : BookProof.SmGaugeRep.smGenP_closes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:58:46.872537+00:00
-- url     : https://prove2.me/theorems/87573174-8cf4-4d57-a0ac-5f563791a9d9
-- title:
--   `BookProof.SmGaugeRep.smGenP_closes` (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) (A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) : smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.smGenP_closes` (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) (A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) : smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A = Complex.I • ∑ C, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B C : ℝ) : ℂ) • smGenP S3 y C
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.smGenP_closes`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.smGenP_closes
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsSU3
open BookProof.ChapterParitySU2
open BookProof.SmBrstGhost
open BookProof.YangMillsSU3
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.smGenP_closes (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ)
    (A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) :
    smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A
      = Complex.I • ∑ C, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B C : ℝ) : ℂ)
          • smGenP S3 y C := by sorry
