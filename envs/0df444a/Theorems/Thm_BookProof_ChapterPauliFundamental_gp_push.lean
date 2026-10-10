-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_gp_push
-- name    : BookProof.ChapterPauliFundamental.gp_push
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:14.58098+00:00
-- url     : https://prove2.me/theorems/c904f3d3-106d-4407-a78e-3b5c264d215b
-- title:
--   `BookProof.ChapterPauliFundamental.gp_push` (hA : IsCliffordC A) (μ : Fin 4) : ∀ l : List (Fin 4), (∀ ν ∈ l, ν ≠ μ) → A μ * gp A l = ((-1 : ℂ) ^ l.length) • (gp A l * A μ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.gp_push` (hA : IsCliffordC A) (μ : Fin 4) : ∀ l : List (Fin 4), (∀ ν ∈ l, ν ≠ μ) → A μ * gp A l = ((-1 : ℂ) ^ l.length) • (gp A l * A μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.gp_push`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.gp_push
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.gp_push (hA : IsCliffordC A) (μ : Fin 4) :
    ∀ l : List (Fin 4), (∀ ν ∈ l, ν ≠ μ) →
      A μ * gp A l = ((-1 : ℂ) ^ l.length) • (gp A l * A μ) := by sorry
