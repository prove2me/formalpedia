-- Prove2me | Theorems.Thm_BookProof_ChapterA3r_trace_permMat
-- name    : BookProof.ChapterA3r.trace_permMat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:35:59.760984+00:00
-- url     : https://prove2.me/theorems/fff86497-e82b-4cf5-a02c-b487ead9d473
-- title:
--   `BookProof.ChapterA3r.trace_permMat` {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix.trace (permMat σ) = ((Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3r`.
--
--   `BookProof.ChapterA3r.trace_permMat` {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix.trace (permMat σ) = ((Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3r.trace_permMat`.

-- Generated from ChapterA3r.lean — theorem BookProof.ChapterA3r.trace_permMat
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3r
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.ChapterA3r


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q

theorem BookProof.ChapterA3r.trace_permMat {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (permMat σ) =
      ((Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card : ℂ) := by sorry
