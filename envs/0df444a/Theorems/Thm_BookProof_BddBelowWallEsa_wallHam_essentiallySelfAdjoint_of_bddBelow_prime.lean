-- Prove2me | Theorems.Thm_BookProof_BddBelowWallEsa_wallHam_essentiallySelfAdjoint_of_bddBelow_prime
-- name    : BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:15:31.166815+00:00
-- url     : https://prove2.me/theorems/87f47c83-37b6-4bac-9a0c-fa3a60678868
-- title:
--   BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow'
-- statement:
--   BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow'

-- Generated from ChapterBddBelowWallEsa.lean — theorem BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Mathlib
import Definitions.Def_ChapterBddBelowWallEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.BddBelowWallEsa



open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

variable {V : ℝ → ℝ} {z : ℂ} {W W' : ℝ → ℂ}

theorem BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow_prime (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVb : BddBelow (Set.range V)) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by sorry
