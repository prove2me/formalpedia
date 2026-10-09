-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussDer_apply
-- name    : BookProof.BookBrstYangMills.gaussDer_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:20:17.809978+00:00
-- url     : https://prove2.me/theorems/2486a614-c9ed-44e2-bfa9-fc2c6cdca4e4
-- title:
--   `BookProof.BookBrstYangMills.gaussDer_apply` (c : Fin N) (p : FieldPoly N) : gaussDer G c p = ∑ i : Fin 4 × Fin N, gaussVec G c i * pderiv i p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussDer_apply` (c : Fin N) (p : FieldPoly N) : gaussDer G c p = ∑ i : Fin 4 × Fin N, gaussVec G c i * pderiv i p
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussDer_apply`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussDer_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gaussDer_apply (c : Fin N) (p : FieldPoly N) :
    gaussDer G c p = ∑ i : Fin 4 × Fin N, gaussVec G c i * pderiv i p := by sorry
