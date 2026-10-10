-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_sel_lo_ne
-- name    : BookProof.ChapterPauliFundamental.sel_lo_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:58.334979+00:00
-- url     : https://prove2.me/theorems/86697e9b-0199-412e-838c-a43baae8abd6
-- title:
--   `BookProof.ChapterPauliFundamental.sel_lo_ne` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), ∀ ν ∈ sel (lo μ T), ν ≠ μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.sel_lo_ne` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), ∀ ν ∈ sel (lo μ T), ν ≠ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.sel_lo_ne`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.sel_lo_ne
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.sel_lo_ne : ∀ (μ : Fin 4) (T : Finset (Fin 4)), ∀ ν ∈ sel (lo μ T), ν ≠ μ := by sorry
