-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_pderiv_X_mul
-- name    : BookProof.BookBrstYangMills.pderiv_X_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:19:18.493104+00:00
-- url     : https://prove2.me/theorems/d11ed9ea-e9dc-4039-b6e1-65ecc11359a9
-- title:
--   `BookProof.BookBrstYangMills.pderiv_X_mul` (i j : Fin 4 × Fin N) (p : FieldPoly N) : (pderiv i : Derivation ℂ (FieldPoly N) (FieldPoly N)) (X j * p) = (if i = j then p else 0) + X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.pderiv_X_mul` (i j : Fin 4 × Fin N) (p : FieldPoly N) : (pderiv i : Derivation ℂ (FieldPoly N) (FieldPoly N)) (X j * p) = (if i = j then p else 0) + X j * pderiv i p
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.pderiv_X_mul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.pderiv_X_mul
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.pderiv_X_mul (i j : Fin 4 × Fin N) (p : FieldPoly N) :
    (pderiv i : Derivation ℂ (FieldPoly N) (FieldPoly N)) (X j * p)
      = (if i = j then p else 0) + X j * pderiv i p := by sorry
