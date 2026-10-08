-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bookOmega_eq_brstCharge
-- name    : BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:20:43.887854+00:00
-- url     : https://prove2.me/theorems/e1b67457-e559-41a9-8683-5f63926443b2
-- title:
--   `BookProof.BookBrstYangMills.bookOmega_eq_brstCharge` : bookOmega G = Complex.I • brstCharge G.f (gaussGen G) chiOp betaOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bookOmega_eq_brstCharge` : bookOmega G = Complex.I • brstCharge G.f (gaussGen G) chiOp betaOp
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bookOmega_eq_brstCharge`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.BRSTNilpotent
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.YangMillsGhost
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.bookOmega_eq_brstCharge :
    bookOmega G = Complex.I • brstCharge G.f (gaussGen G) chiOp betaOp := by sorry
