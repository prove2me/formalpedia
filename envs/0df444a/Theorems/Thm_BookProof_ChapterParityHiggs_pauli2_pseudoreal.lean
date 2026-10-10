-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_pauli2_pseudoreal
-- name    : BookProof.ChapterParityHiggs.pauli2_pseudoreal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:07:12.950567+00:00
-- url     : https://prove2.me/theorems/f9cce26a-f1a0-43e7-be25-cc83eb4480a5
-- title:
--   `BookProof.ChapterParityHiggs.pauli2_pseudoreal` : pauli2 * (pauli2.map (starRingEnd ℂ)) = -1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.pauli2_pseudoreal` : pauli2 * (pauli2.map (starRingEnd ℂ)) = -1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.pauli2_pseudoreal`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.pauli2_pseudoreal
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParity
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.pauli2_pseudoreal : pauli2 * (pauli2.map (starRingEnd ℂ)) = -1 := by sorry
