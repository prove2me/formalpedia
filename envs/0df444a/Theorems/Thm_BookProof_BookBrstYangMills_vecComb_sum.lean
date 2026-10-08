-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_vecComb_sum
-- name    : BookProof.BookBrstYangMills.vecComb_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:14:50.622548+00:00
-- url     : https://prove2.me/theorems/99789ca1-e7cb-4e8a-943b-f0bd5a995a42
-- title:
--   `BookProof.BookBrstYangMills.vecComb_sum` {n : ℕ} (κ : Fin n → ℝ) (α : Fin n → ℝ) (β : Fin n → Fin N → ℝ) (μ : Fin 4) : (∑ h, ((κ h : ℝ) : ℂ) • vecComb (α h) (β h)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.vecComb_sum` {n : ℕ} (κ : Fin n → ℝ) (α : Fin n → ℝ) (β : Fin n → Fin N → ℝ) (μ : Fin 4) : (∑ h, ((κ h : ℝ) : ℂ) • vecComb (α h) (β h) μ) = vecComb (∑ h, κ h * α h) (fun g => ∑ h, κ h * β h g) μ
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.vecComb_sum`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.vecComb_sum
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.vecComb_sum {n : ℕ} (κ : Fin n → ℝ) (α : Fin n → ℝ) (β : Fin n → Fin N → ℝ)
    (μ : Fin 4) :
    (∑ h, ((κ h : ℝ) : ℂ) • vecComb (α h) (β h) μ)
      = vecComb (∑ h, κ h * α h) (fun g => ∑ h, κ h * β h g) μ := by sorry
