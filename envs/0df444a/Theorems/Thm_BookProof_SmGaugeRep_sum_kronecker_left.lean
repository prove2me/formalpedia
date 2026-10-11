-- Prove2me | Theorems.Thm_BookProof_SmGaugeRep_sum_kronecker_left
-- name    : BookProof.SmGaugeRep.sum_kronecker_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:57:18.735811+00:00
-- url     : https://prove2.me/theorems/8e79437e-8b2a-4ee8-ba5d-198bb525f056
-- title:
--   `BookProof.SmGaugeRep.sum_kronecker_left` {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeRepresentation`.
--
--   `BookProof.SmGaugeRep.sum_kronecker_left` {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i ⊗ₖ B)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeRep.sum_kronecker_left`.

-- Generated from ChapterSmGaugeRepresentation.lean — theorem BookProof.SmGaugeRep.sum_kronecker_left
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
open BookProof.SmGaugeRep



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

theorem BookProof.SmGaugeRep.sum_kronecker_left {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i ⊗ₖ B) := by sorry
