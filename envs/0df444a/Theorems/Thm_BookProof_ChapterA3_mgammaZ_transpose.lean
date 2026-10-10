-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgammaZ_transpose
-- name    : BookProof.ChapterA3.mgammaZ_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:44.691307+00:00
-- url     : https://prove2.me/theorems/eaaa86dd-a707-46f8-b261-faa5ff83a2d8
-- title:
--   `BookProof.ChapterA3.mgammaZ_transpose` (μ : Fin 4) : (mgammaZ μ)ᵀ = (if μ = 0 then (-1 : ℤ) else 1) • mgammaZ μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgammaZ_transpose` (μ : Fin 4) : (mgammaZ μ)ᵀ = (if μ = 0 then (-1 : ℤ) else 1) • mgammaZ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgammaZ_transpose`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgammaZ_transpose
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgammaZ_transpose (μ : Fin 4) :
    (mgammaZ μ)ᵀ = (if μ = 0 then (-1 : ℤ) else 1) • mgammaZ μ := by sorry
