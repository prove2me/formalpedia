-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_elimTorsion_eq_gaugeReduce
-- name    : BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T02:09:52.607543+00:00
-- url     : https://prove2.me/theorems/7eeea4e5-12e2-41b6-b385-c89c9fc1594b
-- title:
--   `BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce` (k : Mom) (mu nu i : Fin 3) (x : CMode) : elimTorsion k mu nu i x = gaugeReduce (extTorsionCoef k mu nu i) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce` (k : Mom) (mu nu i : Fin 3) (x : CMode) : elimTorsion k mu nu i x = gaugeReduce (extTorsionCoef k mu nu i) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
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
import Definitions.Def_ChapterQgBrstDerivativeGaugeV2



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL
open BookProof.QgBrstDerivativeGauge

noncomputable section

theorem BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce (k : Mom) (mu nu i : Fin 3) (x : CMode) :
    elimTorsion k mu nu i x = gaugeReduce (extTorsionCoef k mu nu i) x := by sorry
