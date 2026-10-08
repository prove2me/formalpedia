-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_sum_smul_der_apply
-- name    : BookProof.BookBrstYangMills.sum_smul_der_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:15:23.250367+00:00
-- url     : https://prove2.me/theorems/6230630c-fab6-4243-be0e-1a577a20c663
-- title:
--   `BookProof.BookBrstYangMills.sum_smul_der_apply` {n : ℕ} (k : Fin n → ℂ) (D : Fin n → Derivation ℂ (FieldPoly N) (FieldPoly N)) (p : FieldPoly N) : (∑ h, k h • D h) p = ∑ h, k h •
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.sum_smul_der_apply` {n : ℕ} (k : Fin n → ℂ) (D : Fin n → Derivation ℂ (FieldPoly N) (FieldPoly N)) (p : FieldPoly N) : (∑ h, k h • D h) p = ∑ h, k h • (D h) p
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.sum_smul_der_apply`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.sum_smul_der_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.sum_smul_der_apply {n : ℕ} (k : Fin n → ℂ)
    (D : Fin n → Derivation ℂ (FieldPoly N) (FieldPoly N)) (p : FieldPoly N) :
    (∑ h, k h • D h) p = ∑ h, k h • (D h) p := by sorry
