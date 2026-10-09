-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasAdLambda_of_intModel
-- name    : BookProof.ChapterA3.hasAdLambda_of_intModel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:43:35.969984+00:00
-- url     : https://prove2.me/theorems/dfb40f65-a0ad-4342-9a43-fe6cd8377cf7
-- title:
--   `BookProof.ChapterA3.hasAdLambda_of_intModel` (Gz Az : Matrix (Fin 4) (Fin 4) ℤ) (hconj : ∀ μ, Gz * mgammaZ μ - mgammaZ μ * Gz = ∑ ν, Az μ ν • mgammaZ ν) : HasAdLambda ((Int.castRi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.hasAdLambda_of_intModel` (Gz Az : Matrix (Fin 4) (Fin 4) ℤ) (hconj : ∀ μ, Gz * mgammaZ μ - mgammaZ μ * Gz = ∑ ν, Az μ ν • mgammaZ ν) : HasAdLambda ((Int.castRingHom ℝ).mapMatrix Gz) ((Int.castRingHom ℝ).mapMatrix Az)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasAdLambda_of_intModel`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.hasAdLambda_of_intModel
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.hasAdLambda_of_intModel (Gz Az : Matrix (Fin 4) (Fin 4) ℤ)
    (hconj : ∀ μ, Gz * mgammaZ μ - mgammaZ μ * Gz = ∑ ν, Az μ ν • mgammaZ ν) :
    HasAdLambda ((Int.castRingHom ℝ).mapMatrix Gz)
      ((Int.castRingHom ℝ).mapMatrix Az) := by sorry
