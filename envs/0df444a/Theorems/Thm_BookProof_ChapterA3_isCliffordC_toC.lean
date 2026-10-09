-- Prove2me | Theorems.Thm_BookProof_ChapterA3_isCliffordC_toC
-- name    : BookProof.ChapterA3.isCliffordC_toC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:42:53.037458+00:00
-- url     : https://prove2.me/theorems/19f2b21a-f010-411f-bf47-d3e0d60af1ff
-- title:
--   `BookProof.ChapterA3.isCliffordC_toC` {A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hA : IsCliffordR A) : IsCliffordC (fun μ => toC (A μ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.isCliffordC_toC` {A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hA : IsCliffordR A) : IsCliffordC (fun μ => toC (A μ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.isCliffordC_toC`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.isCliffordC_toC
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.isCliffordC_toC {A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hA : IsCliffordR A) :
    IsCliffordC (fun μ => toC (A μ)) := by sorry
