-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_inner_eq_zero_of_le_orthogonal
-- name    : BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:17.335393+00:00
-- url     : https://prove2.me/theorems/a5585a87-ac40-4ee3-ac3b-f29ff5c8a11d
-- title:
--   `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal` {M N : Submodule ℂ H} (h : M ≤ Nᗮ) {a b : H} (ha : a ∈ M) (hb : b ∈ N) : inner ℂ a b = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal` {M N : Submodule ℂ H} (h : M ≤ Nᗮ) {a b : H} (ha : a ∈ M) (hb : b ∈ N) : inner ℂ a b = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
open BookProof.ChapterSpectralDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

theorem BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal {M N : Submodule ℂ H} (h : M ≤ Nᗮ) {a b : H}
    (ha : a ∈ M) (hb : b ∈ N) : inner ℂ a b = 0 := by sorry
