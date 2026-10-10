-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyInverse_invCayleyOp_cayley
-- name    : BookProof.ChapterCayleyInverse.invCayleyOp_cayley
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:42:06.013425+00:00
-- url     : https://prove2.me/theorems/7ea2d7bf-a362-4e0e-932b-eb478bba8f44
-- title:
--   `BookProof.ChapterCayleyInverse.invCayleyOp_cayley` (x : T.domain) (hmem : (x : H) ∈ invCayleyDomain (cayley T)) : invCayleyOp (cayley T) (oneSubU_cayley_injective T) ⟨(x : H), hme
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyInverse`.
--
--   `BookProof.ChapterCayleyInverse.invCayleyOp_cayley` (x : T.domain) (hmem : (x : H) ∈ invCayleyDomain (cayley T)) : invCayleyOp (cayley T) (oneSubU_cayley_injective T) ⟨(x : H), hmem⟩ = T.op x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyInverse.invCayleyOp_cayley`.

-- Generated from ChapterCayleyInverse.lean — theorem BookProof.ChapterCayleyInverse.invCayleyOp_cayley
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_ChapterCayleyInverse_oneSubU_cayley_injective
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

theorem BookProof.ChapterCayleyInverse.invCayleyOp_cayley (x : T.domain) (hmem : (x : H) ∈ invCayleyDomain (cayley T)) :
    invCayleyOp (cayley T) (oneSubU_cayley_injective T) ⟨(x : H), hmem⟩ = T.op x := by sorry
