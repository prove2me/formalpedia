-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_spatial_anticomm
-- name    : BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:55:26.824983+00:00
-- url     : https://prove2.me/theorems/4aa25626-c757-4c12-9572-83e5728abfc4
-- title:
--   `BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm` (i : Fin 3) : dgamma 0 * dgamma i.succ = -(dgamma i.succ * dgamma 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaFourier`.
--
--   `BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm` (i : Fin 3) : dgamma 0 * dgamma i.succ = -(dgamma i.succ * dgamma 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm`.

-- Generated from ChapterMajoranaFourier.lean — theorem BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaFourier.gamma0_spatial_anticomm (i : Fin 3) :
    dgamma 0 * dgamma i.succ = -(dgamma i.succ * dgamma 0) := by sorry
