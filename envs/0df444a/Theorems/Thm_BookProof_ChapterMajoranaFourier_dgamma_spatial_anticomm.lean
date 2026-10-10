-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaFourier_dgamma_spatial_anticomm
-- name    : BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:56:04.775122+00:00
-- url     : https://prove2.me/theorems/49f2ab51-ec65-4469-be3a-ff258c3707c4
-- title:
--   `BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm` (i j : Fin 3) (h : i ≠ j) : dgamma i.succ * dgamma j.succ = -(dgamma j.succ * dgamma i.succ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaFourier`.
--
--   `BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm` (i j : Fin 3) (h : i ≠ j) : dgamma i.succ * dgamma j.succ = -(dgamma j.succ * dgamma i.succ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm`.

-- Generated from ChapterMajoranaFourier.lean — theorem BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm (i j : Fin 3) (h : i ≠ j) :
    dgamma i.succ * dgamma j.succ = -(dgamma j.succ * dgamma i.succ) := by sorry
