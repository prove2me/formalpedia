-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_AfieldPoly_apply
-- name    : BookProof.BookBrstYangMills.AfieldPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:13:54.634976+00:00
-- url     : https://prove2.me/theorems/c39e4d63-64f3-47e8-a477-a652fac49b45
-- title:
--   `BookProof.BookBrstYangMills.AfieldPoly_apply` (μ : Fin 4) (a : Fin N) (p : FieldPoly N) : AfieldPoly μ a p = X (μ, a) * p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.AfieldPoly_apply` (μ : Fin 4) (a : Fin N) (p : FieldPoly N) : AfieldPoly μ a p = X (μ, a) * p
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.AfieldPoly_apply`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.AfieldPoly_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.AfieldPoly_apply (μ : Fin 4) (a : Fin N) (p : FieldPoly N) :
    AfieldPoly μ a p = X (μ, a) * p := by sorry
