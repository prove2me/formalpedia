-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_conjTranspose
-- name    : BookProof.ChapterA3.mgamma_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:13.486067+00:00
-- url     : https://prove2.me/theorems/202ca77e-f647-465b-93bd-f6a8b4fcef02
-- title:
--   `BookProof.ChapterA3.mgamma_conjTranspose` (μ : Fin 4) : (mgamma μ)ᴴ = (if μ = 0 then (-1 : ℂ) else 1) • mgamma μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgamma_conjTranspose` (μ : Fin 4) : (mgamma μ)ᴴ = (if μ = 0 then (-1 : ℂ) else 1) • mgamma μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_conjTranspose`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgamma_conjTranspose
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_conjTranspose (μ : Fin 4) :
    (mgamma μ)ᴴ = (if μ = 0 then (-1 : ℂ) else 1) • mgamma μ := by sorry
