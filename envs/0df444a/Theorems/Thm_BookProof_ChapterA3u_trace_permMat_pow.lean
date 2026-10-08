-- Prove2me | Theorems.Thm_BookProof_ChapterA3u_trace_permMat_pow
-- name    : BookProof.ChapterA3u.trace_permMat_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:37:09.630919+00:00
-- url     : https://prove2.me/theorems/72cfd021-3146-4de0-b51c-82c2a249e7c4
-- title:
--   `BookProof.ChapterA3u.trace_permMat_pow` {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix.trace (permMat σ) = ((4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) : ℕ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3u`.
--
--   `BookProof.ChapterA3u.trace_permMat_pow` {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix.trace (permMat σ) = ((4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) : ℕ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3u.trace_permMat_pow`.

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.trace_permMat_pow
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

theorem BookProof.ChapterA3u.trace_permMat_pow {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (permMat σ)
      = ((4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) : ℕ) : ℂ) := by sorry
