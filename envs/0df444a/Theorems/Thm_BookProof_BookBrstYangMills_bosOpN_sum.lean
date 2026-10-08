-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sum
-- name    : BookProof.BookBrstYangMills.bosOpN_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:12:18.256416+00:00
-- url     : https://prove2.me/theorems/4a35e554-f048-4eb0-956c-0232bf463b70
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_sum` {n : ℕ} (T : Fin n → Module.End ℂ (FieldPoly N)) : bosOpN (∑ e, T e) = ∑ e, bosOpN (T e)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_sum` {n : ℕ} (T : Fin n → Module.End ℂ (FieldPoly N)) : bosOpN (∑ e, T e) = ∑ e, bosOpN (T e)
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_sum`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_sum
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

theorem BookProof.BookBrstYangMills.bosOpN_sum {n : ℕ} (T : Fin n → Module.End ℂ (FieldPoly N)) :
    bosOpN (∑ e, T e) = ∑ e, bosOpN (T e) := by sorry
