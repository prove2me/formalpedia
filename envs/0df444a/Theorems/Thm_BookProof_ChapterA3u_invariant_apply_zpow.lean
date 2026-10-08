-- Prove2me | Theorems.Thm_BookProof_ChapterA3u_invariant_apply_zpow
-- name    : BookProof.ChapterA3u.invariant_apply_zpow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:37:05.25029+00:00
-- url     : https://prove2.me/theorems/b7a75b98-5ad8-401a-bf8b-63d732d1e0d0
-- title:
--   `BookProof.ChapterA3u.invariant_apply_zpow` {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N} (ha : a ∘ σ = a) (k : ℤ) (x : Fin N) : a ((σ ^ k) x) = a x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3u`.
--
--   `BookProof.ChapterA3u.invariant_apply_zpow` {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N} (ha : a ∘ σ = a) (k : ℤ) (x : Fin N) : a ((σ ^ k) x) = a x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3u.invariant_apply_zpow`.

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.invariant_apply_zpow
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

theorem BookProof.ChapterA3u.invariant_apply_zpow {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) (k : ℤ) (x : Fin N) : a ((σ ^ k) x) = a x := by sorry
