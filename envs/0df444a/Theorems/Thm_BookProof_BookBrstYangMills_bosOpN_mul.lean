-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_mul
-- name    : BookProof.BookBrstYangMills.bosOpN_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:11:12.88267+00:00
-- url     : https://prove2.me/theorems/4350d6f9-4f39-4503-98a2-ee3d68ac9839
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_mul` (S T : Module.End ℂ (FieldPoly N)) : bosOpN (S * T) = bosOpN S * bosOpN T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_mul` (S T : Module.End ℂ (FieldPoly N)) : bosOpN (S * T) = bosOpN S * bosOpN T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_mul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_mul
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

theorem BookProof.BookBrstYangMills.bosOpN_mul (S T : Module.End ℂ (FieldPoly N)) :
    bosOpN (S * T) = bosOpN S * bosOpN T := by sorry
