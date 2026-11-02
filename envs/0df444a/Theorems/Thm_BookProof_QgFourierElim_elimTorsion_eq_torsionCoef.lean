-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_elimTorsion_eq_torsionCoef
-- name    : BookProof.QgFourierElim.elimTorsion_eq_torsionCoef
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T21:27:48.291013+00:00
-- url     : https://prove2.me/theorems/ee70dcb2-ea49-493a-aaea-1a669372abe9
-- title:
--   `BookProof.QgFourierElim.elimTorsion_eq_torsionCoef` (k : Mom) (mu nu i : Fin 3) (z : CMode) : elimTorsion k mu nu i z = if z.1 = k then torsionCoef k mu nu i z else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.elimTorsion_eq_torsionCoef` (k : Mom) (mu nu i : Fin 3) (z : CMode) : elimTorsion k mu nu i z = if z.1 = k then torsionCoef k mu nu i z else 0
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.elimTorsion_eq_torsionCoef`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.elimTorsion_eq_torsionCoef
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterQgOuterFockFlow



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

theorem BookProof.QgFourierElim.elimTorsion_eq_torsionCoef (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    elimTorsion k mu nu i z = if z.1 = k then torsionCoef k mu nu i z else 0 := by sorry
