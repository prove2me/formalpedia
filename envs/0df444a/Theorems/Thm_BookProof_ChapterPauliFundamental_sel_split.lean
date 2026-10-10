-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_sel_split
-- name    : BookProof.ChapterPauliFundamental.sel_split
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:14.140979+00:00
-- url     : https://prove2.me/theorems/b79e63f1-2b29-4c91-addb-85f31ec43d32
-- title:
--   `BookProof.ChapterPauliFundamental.sel_split` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), sel T = sel (lo μ T) ++ sel (hi μ T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.sel_split` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), sel T = sel (lo μ T) ++ sel (hi μ T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.sel_split`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.sel_split
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.sel_split : ∀ (μ : Fin 4) (T : Finset (Fin 4)),
    sel T = sel (lo μ T) ++ sel (hi μ T) := by sorry
