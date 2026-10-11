-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_sm_brst_nilpotent_of_su3_relations
-- name    : BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:57:04.835084+00:00
-- url     : https://prove2.me/theorems/fd6f819a-daa2-46d6-a52a-8cfd683f0869
-- title:
--   `BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} (hS3 : TraceOrthonormal S3) (hf3 : ClosesWithStructureConstants S3 f3) (hT
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} (hS3 : TraceOrthonormal S3) (hf3 : ClosesWithStructureConstants S3 f3) (hT : ClosesWithStructureConstants T (smStruct f3)) : smBrstCharge m T f3 * smBrstCharge m T f3 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost
open BookProof.SmCar
open BookProof.YangMillsSU3
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    (hS3 : TraceOrthonormal S3) (hf3 : ClosesWithStructureConstants S3 f3)
    (hT : ClosesWithStructureConstants T (smStruct f3)) :
    smBrstCharge m T f3 * smBrstCharge m T f3 = 0 := by sorry
