-- Prove2me | Theorems.Thm_BookProof_ChapterA4f_boostZ_preserves_angle
-- name    : BookProof.ChapterA4f.boostZ_preserves_angle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:42:53.276981+00:00
-- url     : https://prove2.me/theorems/78c9ba0d-4e40-47be-8caf-5cfb58cdfe65
-- title:
--   `BookProof.ChapterA4f.boostZ_preserves_angle` {l : ℂ} (hl : l ≠ 0) (T : Matrix (Fin 2) (Fin 2) ℂ) : (boostZ l * T * boostZ l⁻¹) 0 0 = T 0 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4f`.
--
--   `BookProof.ChapterA4f.boostZ_preserves_angle` {l : ℂ} (hl : l ≠ 0) (T : Matrix (Fin 2) (Fin 2) ℂ) : (boostZ l * T * boostZ l⁻¹) 0 0 = T 0 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4f.boostZ_preserves_angle`.

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_preserves_angle
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4f.boostZ_preserves_angle {l : ℂ} (hl : l ≠ 0) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (boostZ l * T * boostZ l⁻¹) 0 0 = T 0 0 := by sorry
