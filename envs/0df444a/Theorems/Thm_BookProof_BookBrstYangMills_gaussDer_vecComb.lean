-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussDer_vecComb
-- name    : BookProof.BookBrstYangMills.gaussDer_vecComb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:14:59.964792+00:00
-- url     : https://prove2.me/theorems/d10e0591-0651-4148-840e-2b139aa581cd
-- title:
--   `BookProof.BookBrstYangMills.gaussDer_vecComb` (c : Fin N) (α : ℝ) (β : Fin N → ℝ) (μ : Fin 4) : gaussDer G c (vecComb α β μ) = vecComb (∑ b, β b * (-(G.D μ c b))) (fun g => ∑ b, β
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussDer_vecComb` (c : Fin N) (α : ℝ) (β : Fin N → ℝ) (μ : Fin 4) : gaussDer G c (vecComb α β μ) = vecComb (∑ b, β b * (-(G.D μ c b))) (fun g => ∑ b, β b * G.f b g c) μ
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussDer_vecComb`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussDer_vecComb
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gaussDer_vecComb (c : Fin N) (α : ℝ) (β : Fin N → ℝ) (μ : Fin 4) :
    gaussDer G c (vecComb α β μ)
      = vecComb (∑ b, β b * (-(G.D μ c b))) (fun g => ∑ b, β b * G.f b g c) μ := by sorry
