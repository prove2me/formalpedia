-- Prove2me | Theorems.Thm_BookProof_ChapterA3_adjoint_mgammaLin
-- name    : BookProof.ChapterA3.adjoint_mgammaLin
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:36.667007+00:00
-- url     : https://prove2.me/theorems/bbaec769-47a8-42da-805c-e8a53e53101c
-- title:
--   `BookProof.ChapterA3.adjoint_mgammaLin` (μ : Fin 4) : LinearMap.adjoint (mgammaLin μ) = (if μ = 0 then (-1 : ℂ) else 1) • mgammaLin μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.adjoint_mgammaLin` (μ : Fin 4) : LinearMap.adjoint (mgammaLin μ) = (if μ = 0 then (-1 : ℂ) else 1) • mgammaLin μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.adjoint_mgammaLin`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.adjoint_mgammaLin
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.adjoint_mgammaLin (μ : Fin 4) :
    LinearMap.adjoint (mgammaLin μ) = (if μ = 0 then (-1 : ℂ) else 1) • mgammaLin μ := by sorry
