-- Prove2me | Theorems.Thm_BookProof_ChapterA4f_boostZ_conj_mem
-- name    : BookProof.ChapterA4f.boostZ_conj_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:44:21.997558+00:00
-- url     : https://prove2.me/theorems/106b4c43-59a6-4ace-82d6-ab159f4c26b0
-- title:
--   `BookProof.ChapterA4f.boostZ_conj_mem` {l : ℂ} (hl : l ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo) : boostZ l * T * boostZ l⁻¹ ∈ SEtwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4f`.
--
--   `BookProof.ChapterA4f.boostZ_conj_mem` {l : ℂ} (hl : l ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo) : boostZ l * T * boostZ l⁻¹ ∈ SEtwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4f.boostZ_conj_mem`.

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_conj_mem
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4f.boostZ_conj_mem {l : ℂ} (hl : l ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℂ}
    (hT : T ∈ SEtwo) : boostZ l * T * boostZ l⁻¹ ∈ SEtwo := by sorry
