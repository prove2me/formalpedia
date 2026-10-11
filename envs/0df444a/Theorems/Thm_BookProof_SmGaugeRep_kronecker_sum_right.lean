-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_kronecker_sum_right
-- name    : BookProof.SmGaugeRep.kronecker_sum_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:56:42.28586+00:00
-- url     : https://prove2.me/theorems/b379f1a6-4c6e-42ca-80c4-800c266b505e
-- title:
--   `BookProof.SmGaugeRep.kronecker_sum_right` {ι : Type*} (s : Finset ι) (A : Matrix (Fin 3) (Fin 3) ℂ) (B : ι → Matrix (Fin 2) (Fin 2) ℂ) : A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, (A...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.kronecker_sum_right` {ι : Type*} (s : Finset ι) (A : Matrix (Fin 3) (Fin 3) ℂ) (B : ι → Matrix (Fin 2) (Fin 2) ℂ) : A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, (A ⊗ₖ B i)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.kronecker_sum_right`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.kronecker_sum_right
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.kronecker_sum_right {ι : Type*} (s : Finset ι) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, (A ⊗ₖ B i) := by sorry
