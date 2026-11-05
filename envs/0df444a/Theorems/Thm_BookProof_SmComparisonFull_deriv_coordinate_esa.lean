-- Prove2me | Theorems.Thm_BookProof_SmComparisonFull_deriv_coordinate_esa
-- name    : BookProof.SmComparisonFull.deriv_coordinate_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:59:45.490137+00:00
-- url     : https://prove2.me/theorems/465931bc-0a2e-4030-a077-d8d540c0b20d
-- title:
--   `BookProof.SmComparisonFull.deriv_coordinate_esa` : EssentiallySelfAdjointOn (ccDomain ℝ) (opCc (fun x : ℝ => x ^ 2) contDiff_pow2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmComparisonFull`.
--
--   `BookProof.SmComparisonFull.deriv_coordinate_esa` : EssentiallySelfAdjointOn (ccDomain ℝ) (opCc (fun x : ℝ => x ^ 2) contDiff_pow2)
--
--   Formalization note: Lean 4 identifier `BookProof.SmComparisonFull.deriv_coordinate_esa`.

-- Generated from ChapterSmComparisonFull.lean — theorem BookProof.SmComparisonFull.deriv_coordinate_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterSmComparisonFull
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ScalaronEsa



open BookProof.FarisLavine
open BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open MeasureTheory
open BookProof.SmComparison

noncomputable section

theorem BookProof.SmComparisonFull.deriv_coordinate_esa :
    EssentiallySelfAdjointOn (ccDomain ℝ) (opCc (fun x : ℝ => x ^ 2) contDiff_pow2) := by sorry
