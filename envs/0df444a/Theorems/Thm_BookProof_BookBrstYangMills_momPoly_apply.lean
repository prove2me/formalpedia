-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_momPoly_apply
-- name    : BookProof.BookBrstYangMills.momPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:13:46.495984+00:00
-- url     : https://prove2.me/theorems/b6ae7fb0-7960-45d2-b787-7aa34fdf930d
-- title:
--   `BookProof.BookBrstYangMills.momPoly_apply` (μ : Fin 4) (a : Fin N) (p : FieldPoly N) : momPoly μ a p = (-Complex.I) • (pderiv (μ, a) p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.momPoly_apply` (μ : Fin 4) (a : Fin N) (p : FieldPoly N) : momPoly μ a p = (-Complex.I) • (pderiv (μ, a) p)
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.momPoly_apply`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.momPoly_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.momPoly_apply (μ : Fin 4) (a : Fin N) (p : FieldPoly N) :
    momPoly μ a p = (-Complex.I) • (pderiv (μ, a) p) := by sorry
