-- Prove2me | Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
-- name    : BookProof.ChapterPinOmega.qiC_eq_cast
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:25.023484+00:00
-- url     : https://prove2.me/theorems/6b503d63-bd65-413d-8449-91f186b554c1
-- title:
--   `BookProof.ChapterPinOmega.qiC_eq_cast` : qiC = (Int.castRingHom ℂ).mapMatrix qi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPinOmega`.
--
--   `BookProof.ChapterPinOmega.qiC_eq_cast` : qiC = (Int.castRingHom ℂ).mapMatrix qi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPinOmega.qiC_eq_cast`.

-- Generated from ChapterPinOmega.lean — theorem BookProof.ChapterPinOmega.qiC_eq_cast
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinDoubleCover
open BookProof.ChapterPinOmega


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterPinOmega.qiC_eq_cast : qiC = (Int.castRingHom ℂ).mapMatrix qi := by sorry
