-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_denseRange_one_sub_cayley
-- name    : BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:37:20.244995+00:00
-- url     : https://prove2.me/theorems/ab391b22-1437-49cf-8474-83413733108e
-- title:
--   `BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley` : DenseRange (fun y : H => y - cayley T y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley` : DenseRange (fun y : H => y - cayley T y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterCayleyTransform


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley :
    DenseRange (fun y : H => y - cayley T y) := by sorry
