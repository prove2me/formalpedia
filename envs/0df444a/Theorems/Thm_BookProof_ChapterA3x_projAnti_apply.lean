-- Prove2me | Theorems.Thm_BookProof_ChapterA3x_projAnti_apply
-- name    : BookProof.ChapterA3x.projAnti_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:39:54.469398+00:00
-- url     : https://prove2.me/theorems/46bf6b58-3285-4fd4-8310-bd31e0bc7dff
-- title:
--   `BookProof.ChapterA3x.projAnti_apply` {N : ℕ} (a b : Idx N) : projAnti N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), signC σ * (if b = a ∘ σ then (1 : ℂ) else 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3x`.
--
--   `BookProof.ChapterA3x.projAnti_apply` {N : ℕ} (a b : Idx N) : projAnti N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), signC σ * (if b = a ∘ σ then (1 : ℂ) else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3x.projAnti_apply`.

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projAnti_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3x.projAnti_apply {N : ℕ} (a b : Idx N) :
    projAnti N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      signC σ * (if b = a ∘ σ then (1 : ℂ) else 0) := by sorry
