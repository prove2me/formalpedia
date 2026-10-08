-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sum3
-- name    : BookProof.BookBrstYangMills.bosOpN_sum3
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:19:58.068684+00:00
-- url     : https://prove2.me/theorems/3f279e00-2d4a-407b-94ce-4dc3758ebc87
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_sum3` (T : Fin 4 → Fin N → Fin N → Module.End ℂ (FieldPoly N)) : bosOpN (∑ μ, ∑ a, ∑ b, T μ a b) = ∑ μ, ∑ a, ∑ b, bosOpN (T μ a b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_sum3` (T : Fin 4 → Fin N → Fin N → Module.End ℂ (FieldPoly N)) : bosOpN (∑ μ, ∑ a, ∑ b, T μ a b) = ∑ μ, ∑ a, ∑ b, bosOpN (T μ a b)
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_sum3`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_sum3
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

theorem BookProof.BookBrstYangMills.bosOpN_sum3 (T : Fin 4 → Fin N → Fin N → Module.End ℂ (FieldPoly N)) :
    bosOpN (∑ μ, ∑ a, ∑ b, T μ a b) = ∑ μ, ∑ a, ∑ b, bosOpN (T μ a b) := by sorry
