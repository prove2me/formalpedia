-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasAdLambda_sum
-- name    : BookProof.ChapterA3.hasAdLambda_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:45:50.288437+00:00
-- url     : https://prove2.me/theorems/c506a719-fe84-45ee-beaf-5066ea4079c4
-- title:
--   `BookProof.ChapterA3.hasAdLambda_sum` {ι : Type*} (s : Finset ι) (G A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, HasAdLambda (G i) (A i)) : HasAdLambda (∑ i ∈ s, G i) (∑ i ∈ s,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.hasAdLambda_sum` {ι : Type*} (s : Finset ι) (G A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, HasAdLambda (G i) (A i)) : HasAdLambda (∑ i ∈ s, G i) (∑ i ∈ s, A i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasAdLambda_sum`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.hasAdLambda_sum
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.hasAdLambda_sum {ι : Type*} (s : Finset ι)
    (G A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, HasAdLambda (G i) (A i)) :
    HasAdLambda (∑ i ∈ s, G i) (∑ i ∈ s, A i) := by sorry
