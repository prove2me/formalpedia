-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_inter_isUnit
-- name    : BookProof.ChapterPauliFundamental.inter_isUnit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:43.439141+00:00
-- url     : https://prove2.me/theorems/fab79cd1-6aff-43f9-a52f-988dcded93c1
-- title:
--   `BookProof.ChapterPauliFundamental.inter_isUnit` (hA : IsCliffordC A) {F : M4} (hF : inter A F ≠ 0) : IsUnit (inter A F).det
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.inter_isUnit` (hA : IsCliffordC A) {F : M4} (hF : inter A F ≠ 0) : IsUnit (inter A F).det
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.inter_isUnit`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.inter_isUnit
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.inter_isUnit (hA : IsCliffordC A) {F : M4} (hF : inter A F ≠ 0) :
    IsUnit (inter A F).det := by sorry
