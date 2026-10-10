-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_su2_preserves_spatialNormSq
-- name    : BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:33:15.75568+00:00
-- url     : https://prove2.me/theorems/35605679-7776-44a6-a8e8-990ea78ef5c7
-- title:
--   `BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq` {T : Matrix (Fin 2) (Fin 2) ℂ} (hU : Tᴴ * T = 1) (hT : T.det = 1) (x : Fin 4 → ℝ) : spatialNormSq (vecOfMat (spinorAction T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq` {T : Matrix (Fin 2) (Fin 2) ℂ} (hU : Tᴴ * T = 1) (hT : T.det = 1) (x : Fin 4 → ℝ) : spatialNormSq (vecOfMat (spinorAction T (hermMat x))) = spatialNormSq x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq {T : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : Tᴴ * T = 1) (hT : T.det = 1) (x : Fin 4 → ℝ) :
    spatialNormSq (vecOfMat (spinorAction T (hermMat x))) = spatialNormSq x := by sorry
