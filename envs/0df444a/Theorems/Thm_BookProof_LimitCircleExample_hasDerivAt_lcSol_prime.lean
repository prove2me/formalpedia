-- Prove2me | Theorems.Thm_BookProof_LimitCircleExample_hasDerivAt_lcSol_prime
-- name    : BookProof.LimitCircleExample.hasDerivAt_lcSol_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:49:15.364+00:00
-- url     : https://prove2.me/theorems/a36e46e3-8399-4e29-a9fa-be1ca46ae59b
-- title:
--   BookProof.LimitCircleExample.hasDerivAt_lcSol'
-- statement:
--   BookProof.LimitCircleExample.hasDerivAt_lcSol'

-- Generated from ChapterLimitCircleExample.lean — theorem BookProof.LimitCircleExample.hasDerivAt_lcSol'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
open BookProof.LimitCircleExample



open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem BookProof.LimitCircleExample.hasDerivAt_lcSol_prime (x : ℝ) :
    HasDerivAt (fun y => lcLog' y * lcSol y)
      ((((lcV x : ℝ) : ℂ) - Complex.I) * lcSol x) x := by sorry
