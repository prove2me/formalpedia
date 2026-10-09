-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussDer_bracket
-- name    : BookProof.BookBrstYangMills.gaussDer_bracket
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:15:36.28604+00:00
-- url     : https://prove2.me/theorems/52423fda-aa06-4b60-9d9a-b9f231dc89e0
-- title:
--   `BookProof.BookBrstYangMills.gaussDer_bracket` (c e : Fin N) : ⁅gaussDer G c, gaussDer G e⁆ = ∑ h, ((G.f c e h : ℝ) : ℂ) • gaussDer G h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussDer_bracket` (c e : Fin N) : ⁅gaussDer G c, gaussDer G e⁆ = ∑ h, ((G.f c e h : ℝ) : ℂ) • gaussDer G h
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussDer_bracket`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussDer_bracket
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gaussDer_bracket (c e : Fin N) :
    ⁅gaussDer G c, gaussDer G e⁆
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • gaussDer G h := by sorry
