-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilon_apply_comb
-- name    : BookProof.ChapterA3.upsilon_apply_comb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:49:29.256131+00:00
-- url     : https://prove2.me/theorems/fb29b057-87e0-49f5-80cf-5f95527915f0
-- title:
--   `BookProof.ChapterA3.upsilon_apply_comb` (T : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) : Tᴴ * (∑ ν, x ν • pauliσ ν) * T = ∑ μ, (∑ ν, UpsilonC T μ ν * x ν) • pauliσ μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilon_apply_comb` (T : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) : Tᴴ * (∑ ν, x ν • pauliσ ν) * T = ∑ μ, (∑ ν, UpsilonC T μ ν * x ν) • pauliσ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilon_apply_comb`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilon_apply_comb
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilon_apply_comb (T : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) :
    Tᴴ * (∑ ν, x ν • pauliσ ν) * T = ∑ μ, (∑ ν, UpsilonC T μ ν * x ν) • pauliσ μ := by sorry
