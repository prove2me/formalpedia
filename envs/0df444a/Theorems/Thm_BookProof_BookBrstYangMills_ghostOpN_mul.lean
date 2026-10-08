-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_ghostOpN_mul
-- name    : BookProof.BookBrstYangMills.ghostOpN_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:12:42.825001+00:00
-- url     : https://prove2.me/theorems/84a1c243-8a9b-4008-9797-2931984d0678
-- title:
--   `BookProof.BookBrstYangMills.ghostOpN_mul` (S T : Module.End ℂ (GhostSpace N)) : ghostOpN (S * T) = ghostOpN S * ghostOpN T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.ghostOpN_mul` (S T : Module.End ℂ (GhostSpace N)) : ghostOpN (S * T) = ghostOpN S * ghostOpN T
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.ghostOpN_mul`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.ghostOpN_mul
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

theorem BookProof.BookBrstYangMills.ghostOpN_mul (S T : Module.End ℂ (GhostSpace N)) :
    ghostOpN (S * T) = ghostOpN S * ghostOpN T := by sorry
