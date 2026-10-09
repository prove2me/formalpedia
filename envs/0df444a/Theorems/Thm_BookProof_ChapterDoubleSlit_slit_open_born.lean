-- Prove2me | Theorems.Thm_BookProof_ChapterDoubleSlit_slit_open_born
-- name    : BookProof.ChapterDoubleSlit.slit_open_born
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:07:27.377562+00:00
-- url     : https://prove2.me/theorems/7e737cbd-e08f-4209-9344-c039d31211c4
-- title:
--   `BookProof.ChapterDoubleSlit.slit_open_born` : bornProb (H *ᵥ (H *ᵥ psi0)) 0 = 1 ∧ bornProb (H *ᵥ (H *ᵥ psi0)) 1 = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDoubleSlit`.
--
--   `BookProof.ChapterDoubleSlit.slit_open_born` : bornProb (H *ᵥ (H *ᵥ psi0)) 0 = 1 ∧ bornProb (H *ᵥ (H *ᵥ psi0)) 1 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDoubleSlit.slit_open_born`.

-- Generated from ChapterDoubleSlit.lean — theorem BookProof.ChapterDoubleSlit.slit_open_born
import Mathlib
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit


open Matrix
open scoped BigOperators

theorem BookProof.ChapterDoubleSlit.slit_open_born :
    bornProb (H *ᵥ (H *ᵥ psi0)) 0 = 1 ∧ bornProb (H *ᵥ (H *ᵥ psi0)) 1 = 0 := by sorry
