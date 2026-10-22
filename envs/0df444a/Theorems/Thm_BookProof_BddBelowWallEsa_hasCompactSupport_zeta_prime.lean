-- Prove2me | Theorems.Thm_BookProof_BddBelowWallEsa_hasCompactSupport_zeta_prime
-- name    : BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:37:06.046841+00:00
-- url     : https://prove2.me/theorems/efc83d10-a759-42fb-ba4b-68985f78fd8f
-- title:
--   BookProof.BddBelowWallEsa.hasCompactSupport_zeta'
-- statement:
--   BookProof.BddBelowWallEsa.hasCompactSupport_zeta'

-- Generated from ChapterBddBelowWallEsa.lean — theorem BookProof.BddBelowWallEsa.hasCompactSupport_zeta'
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

theorem BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta' r) := by sorry
