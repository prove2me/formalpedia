-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_duhamel
-- name    : BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:02:47.900282+00:00
-- url     : https://prove2.me/theorems/9732b50c-1c92-475d-bf06-c90cb23a1625
-- title:
--   (T S : UnboundedSelfAdjoint H) (chi : T.domain) (t u : ℝ) : HasDerivAt (fun r : ℝ => S.stoneU (t - r) (S.resCLM 1 (T.stoneU r (chi : H)))) (Complex.I • S.stoneU (t - u) (T.resCLM 1...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel (T S : UnboundedSelfAdjoint H) (chi : T.domain) (t u : ℝ) :
    HasDerivAt (fun r : ℝ => S.stoneU (t - r) (S.resCLM 1 (T.stoneU r (chi : H))))
      (Complex.I • S.stoneU (t - u)
        (T.resCLM 1 (T.stoneU u (T.shift 1 chi))
          - S.resCLM 1 (T.stoneU u (T.shift 1 chi)))) u := by sorry
