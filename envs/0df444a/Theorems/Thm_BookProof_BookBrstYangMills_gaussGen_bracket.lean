-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussGen_bracket
-- name    : BookProof.BookBrstYangMills.gaussGen_bracket
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:19:26.254807+00:00
-- url     : https://prove2.me/theorems/3f90deae-26e2-4546-8e58-40dede54eba6
-- title:
--   `BookProof.BookBrstYangMills.gaussGen_bracket` (c e : Fin N) : gaussGen G c * gaussGen G e - gaussGen G e * gaussGen G c = ∑ h, (G.f c e h) • gaussGen G h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussGen_bracket` (c e : Fin N) : gaussGen G c * gaussGen G e - gaussGen G e * gaussGen G c = ∑ h, (G.f c e h) • gaussGen G h
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussGen_bracket`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussGen_bracket
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

theorem BookProof.BookBrstYangMills.gaussGen_bracket (c e : Fin N) :
    gaussGen G c * gaussGen G e - gaussGen G e * gaussGen G c
      = ∑ h, (G.f c e h) • gaussGen G h := by sorry
