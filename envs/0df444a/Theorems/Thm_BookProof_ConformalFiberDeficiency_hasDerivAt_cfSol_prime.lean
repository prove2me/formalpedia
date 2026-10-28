-- Prove2me | Theorems.Thm_BookProof_ConformalFiberDeficiency_hasDerivAt_cfSol_prime
-- name    : BookProof.ConformalFiberDeficiency.hasDerivAt_cfSol_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:16:46.995078+00:00
-- url     : https://prove2.me/theorems/33a9449b-44c1-4856-bcec-1ca01c6dba63
-- title:
--   BookProof.ConformalFiberDeficiency.hasDerivAt_cfSol'
-- statement:
--   BookProof.ConformalFiberDeficiency.hasDerivAt_cfSol'

-- Generated from ChapterConformalFiberDeficiency.lean — theorem BookProof.ConformalFiberDeficiency.hasDerivAt_cfSol'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterConformalFiberDeficiency
import Definitions.Def_ChapterBddBelowFiberSumEsa



open MeasureTheory Real Filter Topology
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem BookProof.ConformalFiberDeficiency.hasDerivAt_cfSol_prime (y : ℝ) :
    HasDerivAt (fun t => cfLog' t * cfSol t)
      ((((cfV y : ℝ) : ℂ) - Complex.I) * cfSol y) y := by sorry
