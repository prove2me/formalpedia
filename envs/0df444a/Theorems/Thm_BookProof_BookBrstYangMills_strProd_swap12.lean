-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_strProd_swap12
-- name    : BookProof.BookBrstYangMills.strProd_swap12
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:09:57.272989+00:00
-- url     : https://prove2.me/theorems/84eb178b-b2b8-42e3-8f81-3770ea4afcce
-- title:
--   `BookProof.BookBrstYangMills.strProd_swap12` (p q r s : Fin N) : strProd G p q r s = -strProd G q p r s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.strProd_swap12` (p q r s : Fin N) : strProd G p q r s = -strProd G q p r s
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.strProd_swap12`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.strProd_swap12
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.strProd_swap12 (p q r s : Fin N) : strProd G p q r s = -strProd G q p r s := by sorry
