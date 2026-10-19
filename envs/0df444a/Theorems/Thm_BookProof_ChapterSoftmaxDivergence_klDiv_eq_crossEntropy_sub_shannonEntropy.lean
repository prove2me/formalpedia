-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxDivergence_klDiv_eq_crossEntropy_sub_shannonEntropy
-- name    : BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:32.913015+00:00
-- url     : https://prove2.me/theorems/b805594f-d3cb-410a-8159-6b51e61ffbf4
-- title:
--   `BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy` {p q : Fin m → ℝ} (hq0 : ∀ j, 0 < q j) : klDiv p q = crossEntropy p q - shannonEntropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxDivergence`.
--
--   `BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy` {p q : Fin m → ℝ} (hq0 : ∀ j, 0 < q j) : klDiv p q = crossEntropy p q - shannonEntropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy`.

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterSoftmaxMaxEntropy
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy {p q : Fin m → ℝ}
    (hq0 : ∀ j, 0 < q j) :
    klDiv p q = crossEntropy p q - shannonEntropy p := by sorry
