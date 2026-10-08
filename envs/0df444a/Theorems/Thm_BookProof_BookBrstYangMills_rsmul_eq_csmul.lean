-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_rsmul_eq_csmul
-- name    : BookProof.BookBrstYangMills.rsmul_eq_csmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:19:57.185005+00:00
-- url     : https://prove2.me/theorems/8ff58ee0-69a4-4242-b84b-3ffbef27054b
-- title:
--   `BookProof.BookBrstYangMills.rsmul_eq_csmul` (r : ℝ) (T : Module.End ℂ (BookState N)) : r • T = ((r : ℝ) : ℂ) • T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.rsmul_eq_csmul` (r : ℝ) (T : Module.End ℂ (BookState N)) : r • T = ((r : ℝ) : ℂ) • T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.rsmul_eq_csmul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.rsmul_eq_csmul
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.YangMillsGhost
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.rsmul_eq_csmul (r : ℝ) (T : Module.End ℂ (BookState N)) :
    r • T = ((r : ℝ) : ℂ) • T := by sorry
