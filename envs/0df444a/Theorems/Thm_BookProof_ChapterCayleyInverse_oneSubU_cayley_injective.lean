-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyInverse_oneSubU_cayley_injective
-- name    : BookProof.ChapterCayleyInverse.oneSubU_cayley_injective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:55.929342+00:00
-- url     : https://prove2.me/theorems/a440a638-c209-431c-9f59-6587c2811628
-- title:
--   `BookProof.ChapterCayleyInverse.oneSubU_cayley_injective` : Function.Injective (oneSubU (cayley T))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyInverse`.
--
--   `BookProof.ChapterCayleyInverse.oneSubU_cayley_injective` : Function.Injective (oneSubU (cayley T))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyInverse.oneSubU_cayley_injective`.

-- Generated from ChapterCayleyInverse.lean — theorem BookProof.ChapterCayleyInverse.oneSubU_cayley_injective
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleyTransform
open BookProof.ChapterCayleyInverse


open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (V : H ≃ₗᵢ[ℂ] H)
variable (hinj : Function.Injective (oneSubU V))
variable [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterCayleyInverse.oneSubU_cayley_injective : Function.Injective (oneSubU (cayley T)) := by sorry
