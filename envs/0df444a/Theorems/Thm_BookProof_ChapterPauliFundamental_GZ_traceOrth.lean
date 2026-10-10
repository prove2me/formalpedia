-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_GZ_traceOrth
-- name    : BookProof.ChapterPauliFundamental.GZ_traceOrth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:57.694711+00:00
-- url     : https://prove2.me/theorems/95861743-3e5f-4281-805e-4971939307ab
-- title:
--   `BookProof.ChapterPauliFundamental.GZ_traceOrth` : ∀ S T : Finset (Fin 4), (GZ S * (GZ T)ᵀ).trace = if S = T then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.GZ_traceOrth` : ∀ S T : Finset (Fin 4), (GZ S * (GZ T)ᵀ).trace = if S = T then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.GZ_traceOrth`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.GZ_traceOrth
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.GZ_traceOrth : ∀ S T : Finset (Fin 4),
    (GZ S * (GZ T)ᵀ).trace = if S = T then 4 else 0 := by sorry
