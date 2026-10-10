-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_G_traceOrth
-- name    : BookProof.ChapterPauliFundamental.G_traceOrth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:29:28.360002+00:00
-- url     : https://prove2.me/theorems/97a8a0c2-b713-4c58-8fa9-1648a1594a29
-- title:
--   `BookProof.ChapterPauliFundamental.G_traceOrth` (S T : Finset (Fin 4)) : (G S * (G T)ᵀ).trace = if S = T then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.G_traceOrth` (S T : Finset (Fin 4)) : (G S * (G T)ᵀ).trace = if S = T then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.G_traceOrth`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.G_traceOrth
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.G_traceOrth (S T : Finset (Fin 4)) :
    (G S * (G T)ᵀ).trace = if S = T then 4 else 0 := by sorry
