-- Prove2me | Theorems.Thm_BookProof_BddBelowWallEsa_continuous_zeta_prime
-- name    : BookProof.BddBelowWallEsa.continuous_zeta_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:36:58.041353+00:00
-- url     : https://prove2.me/theorems/9daac3c0-a13c-40ad-a177-b22bfdc70216
-- title:
--   BookProof.BddBelowWallEsa.continuous_zeta'
-- statement:
--   BookProof.BddBelowWallEsa.continuous_zeta'

-- Generated from ChapterBddBelowWallEsa.lean — theorem BookProof.BddBelowWallEsa.continuous_zeta'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Mathlib
import Definitions.Def_ChapterBddBelowWallEsa
open BookProof.BddBelowWallEsa



open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.BddBelowWallEsa.continuous_zeta_prime (r : ℝ) : Continuous (zeta' r) := by sorry
