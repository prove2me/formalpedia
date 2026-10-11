-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_sub_kronecker
-- name    : BookProof.SmGaugeRep.sub_kronecker
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:55.564102+00:00
-- url     : https://prove2.me/theorems/c0d96fb6-18fe-489f-83c9-2d293856a78e
-- title:
--   `BookProof.SmGaugeRep.sub_kronecker` (A B : Matrix (Fin 3) (Fin 3) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.sub_kronecker` (A B : Matrix (Fin 3) (Fin 3) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.sub_kronecker`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.sub_kronecker
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.sub_kronecker (A B : Matrix (Fin 3) (Fin 3) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by sorry
