-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_exists_res_domain_approx
-- name    : BookProof.ChapterSirkTrotterKato.exists_res_domain_approx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:37:01.120559+00:00
-- url     : https://prove2.me/theorems/b0c67319-ecab-48ef-be32-93b931b8159b
-- title:
--   (v : H) {ε : ℝ} (hε : 0 < ε) : ∃ w : T.domain, ‖v - T.resCLM 1 (w : H)‖ < ε
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.exists_res_domain_approx` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.exists_res_domain_approx
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.exists_res_domain_approx (v : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : T.domain, ‖v - T.resCLM 1 (w : H)‖ < ε := by sorry
