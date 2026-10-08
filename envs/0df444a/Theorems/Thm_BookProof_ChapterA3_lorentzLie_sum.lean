-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lorentzLie_sum
-- name    : BookProof.ChapterA3.lorentzLie_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:46:30.593991+00:00
-- url     : https://prove2.me/theorems/97f28dc1-c69e-4988-832c-288e19d354cf
-- title:
--   `BookProof.ChapterA3.lorentzLie_sum` {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, A i ∈ LorentzLie) : (∑ i ∈ s, A i) ∈ LorentzLie
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.lorentzLie_sum` {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, A i ∈ LorentzLie) : (∑ i ∈ s, A i) ∈ LorentzLie
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lorentzLie_sum`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.lorentzLie_sum
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.lorentzLie_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i ∈ s, A i ∈ LorentzLie) : (∑ i ∈ s, A i) ∈ LorentzLie := by sorry
