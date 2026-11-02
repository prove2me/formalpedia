-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_elimTorsion_antisymm
-- name    : BookProof.QgFourierElim.elimTorsion_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T21:27:59.026267+00:00
-- url     : https://prove2.me/theorems/9e6b4fb1-e2b9-4992-89b0-5f7243c0df91
-- title:
--   `BookProof.QgFourierElim.elimTorsion_antisymm` (k : Mom) (mu nu i : Fin 3) (z : CMode) : elimTorsion k nu mu i z = -elimTorsion k mu nu i z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.elimTorsion_antisymm` (k : Mom) (mu nu i : Fin 3) (z : CMode) : elimTorsion k nu mu i z = -elimTorsion k mu nu i z
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.elimTorsion_antisymm`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.elimTorsion_antisymm
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

theorem BookProof.QgFourierElim.elimTorsion_antisymm (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    elimTorsion k nu mu i z = -elimTorsion k mu nu i z := by sorry
