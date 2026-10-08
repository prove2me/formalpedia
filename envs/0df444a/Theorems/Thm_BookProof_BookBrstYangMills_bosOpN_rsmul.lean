-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_rsmul
-- name    : BookProof.BookBrstYangMills.bosOpN_rsmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:12:44.612685+00:00
-- url     : https://prove2.me/theorems/7a9ddc7f-ebf7-43b6-bcb3-9ed1a1fac40f
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_rsmul` (r : ℝ) (T : Module.End ℂ (FieldPoly N)) : bosOpN (r • T) = r • bosOpN T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_rsmul` (r : ℝ) (T : Module.End ℂ (FieldPoly N)) : bosOpN (r • T) = r • bosOpN T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_rsmul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_rsmul
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

theorem BookProof.BookBrstYangMills.bosOpN_rsmul (r : ℝ) (T : Module.End ℂ (FieldPoly N)) :
    bosOpN (r • T) = r • bosOpN T := by sorry
