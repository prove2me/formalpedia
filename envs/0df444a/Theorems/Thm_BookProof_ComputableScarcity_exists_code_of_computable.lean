-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_exists_code_of_computable
-- name    : BookProof.ComputableScarcity.exists_code_of_computable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:19:54.559998+00:00
-- url     : https://prove2.me/theorems/9f66f126-2b74-4a76-9161-26ee288b266b
-- title:
--   `BookProof.ComputableScarcity.exists_code_of_computable` {f : ℕ → ℕ} (hf : Computable f) : ∃ c : Code, evalTotal c = f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.exists_code_of_computable` {f : ℕ → ℕ} (hf : Computable f) : ∃ c : Code, evalTotal c = f
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.exists_code_of_computable`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.exists_code_of_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.exists_code_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, evalTotal c = f := by sorry
