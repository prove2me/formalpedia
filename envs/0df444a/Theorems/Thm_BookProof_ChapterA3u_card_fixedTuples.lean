-- Prove2me | Theorems.Thm_BookProof_ChapterA3u_card_fixedTuples
-- name    : BookProof.ChapterA3u.card_fixedTuples
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:36:54.18338+00:00
-- url     : https://prove2.me/theorems/ab08a6b7-29fe-409d-ac85-5c2e424b2faf
-- title:
--   `BookProof.ChapterA3u.card_fixedTuples` {N : ℕ} (σ : Equiv.Perm (Fin N)) : (Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card = 4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3u`.
--
--   `BookProof.ChapterA3u.card_fixedTuples` {N : ℕ} (σ : Equiv.Perm (Fin N)) : (Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card = 4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3u.card_fixedTuples`.

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.card_fixedTuples
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3r
import Mathlib
import Definitions.Def_ChapterA3u
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.ChapterA3u


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3r

theorem BookProof.ChapterA3u.card_fixedTuples {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card
      = 4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) := by sorry
