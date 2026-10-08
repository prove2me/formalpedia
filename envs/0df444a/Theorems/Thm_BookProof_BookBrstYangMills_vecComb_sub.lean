-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_vecComb_sub
-- name    : BookProof.BookBrstYangMills.vecComb_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:14:56.036803+00:00
-- url     : https://prove2.me/theorems/daacfc88-5a39-472b-8d2f-8ef93a4d8721
-- title:
--   `BookProof.BookBrstYangMills.vecComb_sub` (α α' : ℝ) (β β' : Fin N → ℝ) (μ : Fin 4) : vecComb α β μ - vecComb α' β' μ = vecComb (α - α') (fun g => β g - β' g) μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.vecComb_sub` (α α' : ℝ) (β β' : Fin N → ℝ) (μ : Fin 4) : vecComb α β μ - vecComb α' β' μ = vecComb (α - α') (fun g => β g - β' g) μ
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.vecComb_sub`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.vecComb_sub
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.vecComb_sub (α α' : ℝ) (β β' : Fin N → ℝ) (μ : Fin 4) :
    vecComb α β μ - vecComb α' β' μ = vecComb (α - α') (fun g => β g - β' g) μ := by sorry
