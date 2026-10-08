-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_cayley_apply_ne_self
-- name    : BookProof.ChapterCayleyTransform.cayley_apply_ne_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:36:42.928811+00:00
-- url     : https://prove2.me/theorems/907232f3-bfc9-462c-873c-0d5238e91908
-- title:
--   `BookProof.ChapterCayleyTransform.cayley_apply_ne_self` {y : H} (hy : y ≠ 0) : cayley T y ≠ y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.cayley_apply_ne_self` {y : H} (hy : y ≠ 0) : cayley T y ≠ y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.cayley_apply_ne_self`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.cayley_apply_ne_self
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

theorem BookProof.ChapterCayleyTransform.cayley_apply_ne_self {y : H} (hy : y ≠ 0) : cayley T y ≠ y := by sorry
