-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_smul
-- name    : BookProof.BookBrstYangMills.bosOpN_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:12:13.744304+00:00
-- url     : https://prove2.me/theorems/09e4a612-99ac-4a49-80ec-154a672b2d0f
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_smul` (r : ℂ) (T : Module.End ℂ (FieldPoly N)) : bosOpN (r • T) = r • bosOpN T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_smul` (r : ℂ) (T : Module.End ℂ (FieldPoly N)) : bosOpN (r • T) = r • bosOpN T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_smul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_smul
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

theorem BookProof.BookBrstYangMills.bosOpN_smul (r : ℂ) (T : Module.End ℂ (FieldPoly N)) :
    bosOpN (r • T) = r • bosOpN T := by sorry
