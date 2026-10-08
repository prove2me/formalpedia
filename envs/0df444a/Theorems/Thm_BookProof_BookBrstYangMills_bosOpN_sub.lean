-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sub
-- name    : BookProof.BookBrstYangMills.bosOpN_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:11:36.559595+00:00
-- url     : https://prove2.me/theorems/745052df-c194-45f9-b809-333f216bc90c
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_sub` (S T : Module.End ℂ (FieldPoly N)) : bosOpN (S - T) = bosOpN S - bosOpN T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_sub` (S T : Module.End ℂ (FieldPoly N)) : bosOpN (S - T) = bosOpN S - bosOpN T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_sub`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_sub
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

theorem BookProof.BookBrstYangMills.bosOpN_sub (S T : Module.End ℂ (FieldPoly N)) :
    bosOpN (S - T) = bosOpN S - bosOpN T := by sorry
