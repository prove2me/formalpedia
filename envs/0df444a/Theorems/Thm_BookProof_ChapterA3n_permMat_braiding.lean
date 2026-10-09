-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_permMat_braiding
-- name    : BookProof.ChapterA3n.permMat_braiding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:47.103984+00:00
-- url     : https://prove2.me/theorems/da73447e-ba01-44d7-a727-9e61af94ecdb
-- title:
--   `BookProof.ChapterA3n.permMat_braiding` {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.permMat_braiding` {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.permMat_braiding`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.permMat_braiding
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.permMat_braiding {N : ℕ} (σ : Equiv.Perm (Fin N))
    (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ := by sorry
