-- Prove2me | Theorems.Thm_BookProof_BddBelowWallEsa_hasCompactSupport_zeta_prime_sq
-- name    : BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:37:17.543413+00:00
-- url     : https://prove2.me/theorems/0654d696-a927-43c9-b336-419521c57c21
-- title:
--   BookProof.BddBelowWallEsa.hasCompactSupport_zeta'_sq
-- statement:
--   BookProof.BddBelowWallEsa.hasCompactSupport_zeta'_sq

-- Generated from ChapterBddBelowWallEsa.lean — theorem BookProof.BddBelowWallEsa.hasCompactSupport_zeta'_sq
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

theorem BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime_sq {r : ℝ} (hr : 0 < r) :
    @HasCompactSupport ℝ ℝ _ instMulZeroClassOfSemiring.toZero
      (fun x => (zeta' r x) ^ 2) := by sorry
