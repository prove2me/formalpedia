-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_kronecker_sub
-- name    : BookProof.SmGaugeRep.kronecker_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:56:42.924795+00:00
-- url     : https://prove2.me/theorems/00446fd1-63f5-4309-bce4-f70a8fda53de
-- title:
--   `BookProof.SmGaugeRep.kronecker_sub` (C : Matrix (Fin 3) (Fin 3) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.kronecker_sub` (C : Matrix (Fin 3) (Fin 3) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.kronecker_sub`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.kronecker_sub
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.kronecker_sub (C : Matrix (Fin 3) (Fin 3) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B := by sorry
