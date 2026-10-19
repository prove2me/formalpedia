-- Prove2me | Theorems.Thm_BookProof_ChapterA_qembed_injective
-- name    : BookProof.ChapterA.qembed_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:16:53.513106+00:00
-- url     : https://prove2.me/theorems/9698af0e-2102-4535-a15b-67abe4775a87
-- title:
--   `BookProof.ChapterA.qembed_injective` [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) : Function.Injective (qembed θ hθ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.qembed_injective` [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) : Function.Injective (qembed θ hθ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.qembed_injective`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.qembed_injective
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.qembed_injective [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) :
    Function.Injective (qembed θ hθ) := by sorry
