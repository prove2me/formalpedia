-- Prove2me | Theorems.Thm_BookProof_ChapterA3_bilC_conj
-- name    : BookProof.ChapterA3.bilC_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:53:19.50044+00:00
-- url     : https://prove2.me/theorems/13e202c7-eba0-4666-aa60-e45abce6098c
-- title:
--   `BookProof.ChapterA3.bilC_conj` (A M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) : bilC (Aᵀ * M * A) x = bilC M (fun i => ∑ j, A i j * x j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.bilC_conj` (A M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) : bilC (Aᵀ * M * A) x = bilC M (fun i => ∑ j, A i j * x j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.bilC_conj`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.bilC_conj
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.bilC_conj (A M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) :
    bilC (Aᵀ * M * A) x = bilC M (fun i => ∑ j, A i j * x j) := by sorry
