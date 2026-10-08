-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sum2
-- name    : BookProof.BookBrstYangMills.bosOpN_sum2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:20:13.869625+00:00
-- url     : https://prove2.me/theorems/2e78ef74-fc05-45a1-a3f7-b7092f7bf85c
-- title:
--   `BookProof.BookBrstYangMills.bosOpN_sum2` (T : Fin 4 → Fin N → Module.End ℂ (FieldPoly N)) : bosOpN (∑ μ, ∑ a, T μ a) = ∑ μ, ∑ a, bosOpN (T μ a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.bosOpN_sum2` (T : Fin 4 → Fin N → Module.End ℂ (FieldPoly N)) : bosOpN (∑ μ, ∑ a, T μ a) = ∑ μ, ∑ a, bosOpN (T μ a)
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.bosOpN_sum2`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bosOpN_sum2
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

theorem BookProof.BookBrstYangMills.bosOpN_sum2 (T : Fin 4 → Fin N → Module.End ℂ (FieldPoly N)) :
    bosOpN (∑ μ, ∑ a, T μ a) = ∑ μ, ∑ a, bosOpN (T μ a) := by sorry
