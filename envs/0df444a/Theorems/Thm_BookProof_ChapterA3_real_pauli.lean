-- Prove2me | Theorems.Thm_BookProof_ChapterA3_real_pauli
-- name    : BookProof.ChapterA3.real_pauli
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-06T12:18:42.024538+00:00
-- url     : https://prove2.me/theorems/3ddd568a-8b2e-4558-bb85-7e2369be91fc
-- title:
--   `BookProof.ChapterA3.real_pauli` (hpf : PauliFundamental) (α β : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (hα : IsCliffordR α) (hβ : IsCliffordR β) : ∃ S : Matrix (Fin 4) (Fin 4) ℝ, |S.de
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.real_pauli` (hpf : PauliFundamental) (α β : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (hα : IsCliffordR α) (hβ : IsCliffordR β) : ∃ S : Matrix (Fin 4) (Fin 4) ℝ, |S.det| = 1 ∧ (∀ μ, β μ = S * α μ * S⁻¹) ∧ (∀ S' : Matrix (Fin 4) (Fin 4) ℝ, |S'.det| = 1 → (∀ μ, β μ = S' * α μ * S'⁻¹) → S' = S ∨ S' = -S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.real_pauli`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.real_pauli
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.real_pauli (hpf : PauliFundamental)
    (α β : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (hα : IsCliffordR α) (hβ : IsCliffordR β) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, |S.det| = 1 ∧ (∀ μ, β μ = S * α μ * S⁻¹) ∧
    (∀ S' : Matrix (Fin 4) (Fin 4) ℝ, |S'.det| = 1 → (∀ μ, β μ = S' * α μ * S'⁻¹) →
      S' = S ∨ S' = -S) := by sorry
