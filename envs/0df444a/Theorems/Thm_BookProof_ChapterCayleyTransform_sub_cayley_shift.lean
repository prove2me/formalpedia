-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_sub_cayley_shift
-- name    : BookProof.ChapterCayleyTransform.sub_cayley_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:36:36.069989+00:00
-- url     : https://prove2.me/theorems/93c7368b-f749-43ef-bd3d-adb25b160df0
-- title:
--   `BookProof.ChapterCayleyTransform.sub_cayley_shift` (x : T.domain) : T.shift (-1) x - cayley T (T.shift (-1) x) = (2 * Complex.I) • (x : H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.sub_cayley_shift` (x : T.domain) : T.shift (-1) x - cayley T (T.shift (-1) x) = (2 * Complex.I) • (x : H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.sub_cayley_shift`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.sub_cayley_shift
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

theorem BookProof.ChapterCayleyTransform.sub_cayley_shift (x : T.domain) :
    T.shift (-1) x - cayley T (T.shift (-1) x) = (2 * Complex.I) • (x : H) := by sorry
