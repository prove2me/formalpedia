-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyInverse_invCayleyDomain_cayley
-- name    : BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:37:53.611566+00:00
-- url     : https://prove2.me/theorems/0dae802e-f778-4d06-ba53-85f5fe5f0651
-- title:
--   `BookProof.ChapterCayleyInverse.invCayleyDomain_cayley` : invCayleyDomain (cayley T) = T.domain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyInverse`.
--
--   `BookProof.ChapterCayleyInverse.invCayleyDomain_cayley` : invCayleyDomain (cayley T) = T.domain
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyInverse.invCayleyDomain_cayley`.

-- Generated from ChapterCayleyInverse.lean — theorem BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
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

theorem BookProof.ChapterCayleyInverse.invCayleyDomain_cayley : invCayleyDomain (cayley T) = T.domain := by sorry
