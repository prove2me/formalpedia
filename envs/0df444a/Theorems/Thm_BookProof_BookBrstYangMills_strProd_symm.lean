-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_strProd_symm
-- name    : BookProof.BookBrstYangMills.strProd_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:09:40.191222+00:00
-- url     : https://prove2.me/theorems/72831c45-febe-48cd-83a6-2252be6891d1
-- title:
--   `BookProof.BookBrstYangMills.strProd_symm` (p q r s : Fin N) : strProd G p q r s = strProd G r s p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.strProd_symm` (p q r s : Fin N) : strProd G p q r s = strProd G r s p q
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.strProd_symm`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.strProd_symm
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.strProd_symm (p q r s : Fin N) : strProd G p q r s = strProd G r s p q := by sorry
