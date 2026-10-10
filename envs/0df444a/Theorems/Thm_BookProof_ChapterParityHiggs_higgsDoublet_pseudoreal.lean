-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_higgsDoublet_pseudoreal
-- name    : BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:56.952546+00:00
-- url     : https://prove2.me/theorems/c3b07fc4-90f2-4dbf-a681-86a4a3c9a8d9
-- title:
--   `BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal` (v : Fin 2 → ℂ) : realityOp pauli2 (realityOp pauli2 v) = -v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal` (v : Fin 2 → ℂ) : realityOp pauli2 (realityOp pauli2 v) = -v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParity
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal (v : Fin 2 → ℂ) :
    realityOp pauli2 (realityOp pauli2 v) = -v := by sorry
