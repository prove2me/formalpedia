-- Prove2me | Theorems.Thm_BookProof_ChapterA4f_infinite_spin_excluded
-- name    : BookProof.ChapterA4f.infinite_spin_excluded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:43:09.273235+00:00
-- url     : https://prove2.me/theorems/e776cf91-cf0f-4600-b000-c7db8da4bea8
-- title:
--   `BookProof.ChapterA4f.infinite_spin_excluded` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo) (hc : T 1 0 ≠ 0) : ∀ c : ℂ, c ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ boostZ l * T * boostZ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4f`.
--
--   `BookProof.ChapterA4f.infinite_spin_excluded` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo) (hc : T 1 0 ≠ 0) : ∀ c : ℂ, c ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ boostZ l * T * boostZ l⁻¹ ∈ SEtwo ∧ (boostZ l * T * boostZ l⁻¹) 1 0 = c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4f.infinite_spin_excluded`.

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.infinite_spin_excluded
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4f.infinite_spin_excluded {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo)
    (hc : T 1 0 ≠ 0) :
    ∀ c : ℂ, c ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ boostZ l * T * boostZ l⁻¹ ∈ SEtwo ∧
      (boostZ l * T * boostZ l⁻¹) 1 0 = c := by sorry
