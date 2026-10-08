-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_strProd_swap34
-- name    : BookProof.BookBrstYangMills.strProd_swap34
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:10:01.583722+00:00
-- url     : https://prove2.me/theorems/7f58054c-752e-4af2-b13f-dfeb43f5cf1d
-- title:
--   `BookProof.BookBrstYangMills.strProd_swap34` (p q r s : Fin N) : strProd G p q r s = -strProd G p q s r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.strProd_swap34` (p q r s : Fin N) : strProd G p q r s = -strProd G p q s r
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.strProd_swap34`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.strProd_swap34
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.strProd_swap34 (p q r s : Fin N) : strProd G p q r s = -strProd G p q s r := by sorry
