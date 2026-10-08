-- Prove2me | Theorems.Thm_BookProof_ChapterA3u_invariant_sameCycle
-- name    : BookProof.ChapterA3u.invariant_sameCycle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:36:33.208007+00:00
-- url     : https://prove2.me/theorems/5167c186-c34e-4ce1-9cb9-f97308a2de4d
-- title:
--   `BookProof.ChapterA3u.invariant_sameCycle` {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N} (ha : a ∘ σ = a) {x y : Fin N} (h : σ.SameCycle x y) : a x = a y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3u`.
--
--   `BookProof.ChapterA3u.invariant_sameCycle` {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N} (ha : a ∘ σ = a) {x y : Fin N} (h : σ.SameCycle x y) : a x = a y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3u.invariant_sameCycle`.

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.invariant_sameCycle
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

theorem BookProof.ChapterA3u.invariant_sameCycle {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) {x y : Fin N} (h : σ.SameCycle x y) : a x = a y := by sorry
