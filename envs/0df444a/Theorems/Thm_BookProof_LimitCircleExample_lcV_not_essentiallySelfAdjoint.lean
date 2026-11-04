-- Prove2me | Theorems.Thm_BookProof_LimitCircleExample_lcV_not_essentiallySelfAdjoint
-- name    : BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:54:31.979931+00:00
-- url     : https://prove2.me/theorems/832a849a-3a59-4168-9b10-afc65efc3de8
-- title:
--   `BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint` : ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam lcV contDiff_lcV)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLimitCircleExample`.
--
--   `BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint` : ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam lcV contDiff_lcV)
--
--   Formalization note: Lean 4 identifier `BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint`.

-- Generated from ChapterLimitCircleExample.lean — theorem BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterLimitCircleExample
import Theorems.Thm_BookProof_LimitCircleExample_contDiff_lcV
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.LimitCircleExample



open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint :
    ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam lcV contDiff_lcV) := by sorry
