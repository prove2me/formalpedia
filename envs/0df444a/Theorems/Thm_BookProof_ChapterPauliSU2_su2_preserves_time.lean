-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_su2_preserves_time
-- name    : BookProof.ChapterPauliSU2.su2_preserves_time
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:34:13.351074+00:00
-- url     : https://prove2.me/theorems/3361c216-878e-4b30-bc20-c2fff9c7567e
-- title:
--   `BookProof.ChapterPauliSU2.su2_preserves_time` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1) (x : Fin 4 → ℝ) : (vecOfMat (spinorAction T (hermMat x))) 0 = x 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.su2_preserves_time` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1) (x : Fin 4 → ℝ) : (vecOfMat (spinorAction T (hermMat x))) 0 = x 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.su2_preserves_time`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.su2_preserves_time
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.su2_preserves_time {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1)
    (x : Fin 4 → ℝ) :
    (vecOfMat (spinorAction T (hermMat x))) 0 = x 0 := by sorry
