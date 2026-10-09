-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussGenPoly_bracket
-- name    : BookProof.BookBrstYangMills.gaussGenPoly_bracket
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:15:42.017192+00:00
-- url     : https://prove2.me/theorems/5da9b806-7663-4b2d-bb51-73c91e498a6c
-- title:
--   `BookProof.BookBrstYangMills.gaussGenPoly_bracket` (c e : Fin N) : gaussGenPoly G c * gaussGenPoly G e - gaussGenPoly G e * gaussGenPoly G c = ∑ h, (G.f c e h) • gaussGenPoly G h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussGenPoly_bracket` (c e : Fin N) : gaussGenPoly G c * gaussGenPoly G e - gaussGenPoly G e * gaussGenPoly G c = ∑ h, (G.f c e h) • gaussGenPoly G h
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussGenPoly_bracket`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussGenPoly_bracket
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gaussGenPoly_bracket (c e : Fin N) :
    gaussGenPoly G c * gaussGenPoly G e - gaussGenPoly G e * gaussGenPoly G c
      = ∑ h, (G.f c e h) • gaussGenPoly G h := by sorry
