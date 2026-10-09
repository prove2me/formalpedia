-- Prove2me | Theorems.Thm_BookProof_ChapterCayleyTransform_op_eq_cayley
-- name    : BookProof.ChapterCayleyTransform.op_eq_cayley
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:37:19.044424+00:00
-- url     : https://prove2.me/theorems/4787f238-d695-4d8b-b874-c67cd9df379b
-- title:
--   `BookProof.ChapterCayleyTransform.op_eq_cayley` (x : T.domain) : T.op x = (2 : ℂ)⁻¹ • (T.shift (-1) x + cayley T (T.shift (-1) x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleyTransform`.
--
--   `BookProof.ChapterCayleyTransform.op_eq_cayley` (x : T.domain) : T.op x = (2 : ℂ)⁻¹ • (T.shift (-1) x + cayley T (T.shift (-1) x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleyTransform.op_eq_cayley`.

-- Generated from ChapterCayleyTransform.lean — theorem BookProof.ChapterCayleyTransform.op_eq_cayley
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

theorem BookProof.ChapterCayleyTransform.op_eq_cayley (x : T.domain) :
    T.op x = (2 : ℂ)⁻¹ • (T.shift (-1) x + cayley T (T.shift (-1) x)) := by sorry
