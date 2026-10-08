-- Prove2me | Theorems.Thm_BookProof_ChapterA3x_projSym_apply
-- name    : BookProof.ChapterA3x.projSym_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:39:50.149861+00:00
-- url     : https://prove2.me/theorems/42220ec1-4db2-4c7e-8142-3488fccbee4a
-- title:
--   `BookProof.ChapterA3x.projSym_apply` {N : ℕ} (a b : Idx N) : projSym N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), (if b = a ∘ σ then (1 : ℂ) else 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3x`.
--
--   `BookProof.ChapterA3x.projSym_apply` {N : ℕ} (a b : Idx N) : projSym N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), (if b = a ∘ σ then (1 : ℂ) else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3x.projSym_apply`.

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projSym_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3x.projSym_apply {N : ℕ} (a b : Idx N) :
    projSym N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      (if b = a ∘ σ then (1 : ℂ) else 0) := by sorry
