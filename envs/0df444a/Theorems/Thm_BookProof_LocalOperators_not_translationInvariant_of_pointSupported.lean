-- Prove2me | Theorems.Thm_BookProof_LocalOperators_not_translationInvariant_of_pointSupported
-- name    : BookProof.LocalOperators.not_translationInvariant_of_pointSupported
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:42.954732+00:00
-- url     : https://prove2.me/theorems/5010ba8e-8f14-43f4-a278-c779678741e1
-- title:
--   `BookProof.LocalOperators.not_translationInvariant_of_pointSupported` (hd : 0 < d) (l : LocalField d E) (x₀ : Fin d → ℝ) (hne : l x₀ ≠ 0) (hsupp : ∀ z, z ≠ x₀ → l z = 0) : ¬ Transl
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalOperators`.
--
--   `BookProof.LocalOperators.not_translationInvariant_of_pointSupported` (hd : 0 < d) (l : LocalField d E) (x₀ : Fin d → ℝ) (hne : l x₀ ≠ 0) (hsupp : ∀ z, z ≠ x₀ → l z = 0) : ¬ TranslationInvariant l
--
--   Formalization note: Lean 4 identifier `BookProof.LocalOperators.not_translationInvariant_of_pointSupported`.

-- Generated from ChapterLocalOperators.lean — theorem BookProof.LocalOperators.not_translationInvariant_of_pointSupported
import Mathlib
import Definitions.Def_ChapterLocalOperators
open BookProof.LocalOperators



open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.LocalOperators.not_translationInvariant_of_pointSupported
    (hd : 0 < d) (l : LocalField d E) (x₀ : Fin d → ℝ)
    (hne : l x₀ ≠ 0) (hsupp : ∀ z, z ≠ x₀ → l z = 0) :
    ¬ TranslationInvariant l := by sorry
