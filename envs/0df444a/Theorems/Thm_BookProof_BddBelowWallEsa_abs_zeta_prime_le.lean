-- Prove2me | Theorems.Thm_BookProof_BddBelowWallEsa_abs_zeta_prime_le
-- name    : BookProof.BddBelowWallEsa.abs_zeta_prime_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:48:48.130125+00:00
-- url     : https://prove2.me/theorems/20b80ebb-b0ed-49e7-9a11-0e8be8639258
-- title:
--   BookProof.BddBelowWallEsa.abs_zeta'_le
-- statement:
--   BookProof.BddBelowWallEsa.abs_zeta'_le

-- Generated from ChapterBddBelowWallEsa.lean — theorem BookProof.BddBelowWallEsa.abs_zeta'_le
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

theorem BookProof.BddBelowWallEsa.abs_zeta_prime_le {r : ℝ} (hr : 0 < r) (x : ℝ) : |zeta' r x| ≤ bumpM / r := by sorry
