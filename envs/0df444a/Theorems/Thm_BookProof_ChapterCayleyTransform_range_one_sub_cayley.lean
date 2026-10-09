-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_range_one_sub_cayley
-- name    : BookProof.ChapterCayleyTransform.range_one_sub_cayley
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:36:51.769983+00:00
-- url     : https://prove2.me/theorems/5560fcc1-8a1f-4c3d-8253-eaffb1d8a5a1
-- title:
--   `BookProof.ChapterCayleyTransform.range_one_sub_cayley` : Set.range (fun y : H => y - cayley T y) = (T.domain : Set H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.range_one_sub_cayley` : Set.range (fun y : H => y - cayley T y) = (T.domain : Set H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.range_one_sub_cayley`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.range_one_sub_cayley
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

theorem BookProof.ChapterCayleyTransform.range_one_sub_cayley :
    Set.range (fun y : H => y - cayley T y) = (T.domain : Set H) := by sorry
