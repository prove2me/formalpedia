-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyInverse_cayley_ofUnitary
-- name    : BookProof.ChapterCayleyInverse.cayley_ofUnitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:35:59.577453+00:00
-- url     : https://prove2.me/theorems/a9d0c4b5-8ac9-45a0-a8db-151b669e333b
-- title:
--   `BookProof.ChapterCayleyInverse.cayley_ofUnitary` (hdense : Dense ((invCayleyDomain V : Submodule ℂ H) : Set H)) (y : H) : cayley (ofUnitary V hinj hdense) y = V y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyInverse`.
--
--   `BookProof.ChapterCayleyInverse.cayley_ofUnitary` (hdense : Dense ((invCayleyDomain V : Submodule ℂ H) : Set H)) (y : H) : cayley (ofUnitary V hinj hdense) y = V y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyInverse.cayley_ofUnitary`.

-- Generated from ChapterCayleyInverse.lean — theorem BookProof.ChapterCayleyInverse.cayley_ofUnitary
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

theorem BookProof.ChapterCayleyInverse.cayley_ofUnitary (hdense : Dense ((invCayleyDomain V : Submodule ℂ H) : Set H))
    (y : H) : cayley (ofUnitary V hinj hdense) y = V y := by sorry
