-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lambda_surjective
-- name    : BookProof.ChapterA3.lambda_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:33:51.539137+00:00
-- url     : https://prove2.me/theorems/182c4dc6-8e2b-4ded-b26e-2c95b08eeaf8
-- title:
--   `BookProof.ChapterA3.lambda_surjective` (hpf : PauliFundamental) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) : ∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsPin S ∧ LambdaOf S = Λ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lambda_surjective` (hpf : PauliFundamental) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) : ∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsPin S ∧ LambdaOf S = Λ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lambda_surjective`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lambda_surjective
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lambda_surjective (hpf : PauliFundamental)
    (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsPin S ∧ LambdaOf S = Λ := by sorry
