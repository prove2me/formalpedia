-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_one_sub_cayley_injective
-- name    : BookProof.ChapterCayleyTransform.one_sub_cayley_injective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:13.560882+00:00
-- url     : https://prove2.me/theorems/34f1eddf-4166-4080-9fe1-0c2befa9f67d
-- title:
--   `BookProof.ChapterCayleyTransform.one_sub_cayley_injective` : Function.Injective (fun y : H => y - cayley T y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.one_sub_cayley_injective` : Function.Injective (fun y : H => y - cayley T y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.one_sub_cayley_injective`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.one_sub_cayley_injective
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleyTransform


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterCayleyTransform.one_sub_cayley_injective :
    Function.Injective (fun y : H => y - cayley T y) := by sorry
