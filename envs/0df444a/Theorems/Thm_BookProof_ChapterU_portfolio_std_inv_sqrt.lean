-- Prove2me | Theorems.Thm_BookProof_ChapterU_portfolio_std_inv_sqrt
-- name    : BookProof.ChapterU.portfolio_std_inv_sqrt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:11.635112+00:00
-- url     : https://prove2.me/theorems/0825237c-efe0-4bed-9aa0-d3a26b27914c
-- title:
--   `BookProof.ChapterU.portfolio_std_inv_sqrt` {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) (P : Measure Ω) [IsProbabilityMeasure P] (hindep : ProbabilityTheory.iInde
-- statement:
--   Prove the following Lean 4 theorem from `ChapterU`.
--
--   `BookProof.ChapterU.portfolio_std_inv_sqrt` {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) (P : Measure Ω) [IsProbabilityMeasure P] (hindep : ProbabilityTheory.iIndepFun X P) (hmem : ∀ i, MemLp (X i) 2 P) (hvar : ∀ i, ProbabilityTheory.variance (X i) P = σ ^ 2) : Real.sqrt (ProbabilityTheory.variance (fun ω => (∑ i, X i ω) / n) P) = σ / Real.sqrt n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterU.portfolio_std_inv_sqrt`.

-- Generated from ChapterU.lean — theorem BookProof.ChapterU.portfolio_std_inv_sqrt
import Mathlib
import Definitions.Def_ChapterU
open BookProof.ChapterU


open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]
variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterU.portfolio_std_inv_sqrt {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hindep : ProbabilityTheory.iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hvar : ∀ i, ProbabilityTheory.variance (X i) P = σ ^ 2) :
    Real.sqrt (ProbabilityTheory.variance (fun ω => (∑ i, X i ω) / n) P) = σ / Real.sqrt n := by sorry
