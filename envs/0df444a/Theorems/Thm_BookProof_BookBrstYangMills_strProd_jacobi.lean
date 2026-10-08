-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_strProd_jacobi
-- name    : BookProof.BookBrstYangMills.strProd_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:10:13.26098+00:00
-- url     : https://prove2.me/theorems/9441a789-871b-458b-a5e4-312ce536d82a
-- title:
--   `BookProof.BookBrstYangMills.strProd_jacobi` (x y z w : Fin N) : strProd G x y z w + strProd G y z x w + strProd G z x y w = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.strProd_jacobi` (x y z w : Fin N) : strProd G x y z w + strProd G y z x w + strProd G z x y w = 0
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.strProd_jacobi`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.strProd_jacobi
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.strProd_jacobi (x y z w : Fin N) :
    strProd G x y z w + strProd G y z x w + strProd G z x y w = 0 := by sorry
