-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_momDomain_dense
-- name    : BookProof.NsFieldMomentumInverse.momDomain_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:53:55.524606+00:00
-- url     : https://prove2.me/theorems/e5c3bfba-f70b-4dad-b842-f93cab2f0ea3
-- title:
--   `BookProof.NsFieldMomentumInverse.momDomain_dense` {m : W} (hm : m ≠ 0) : Dense ((momDomain m : Set (Lp ℂ 2 (volume : Measure W))))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.momDomain_dense` {m : W} (hm : m ≠ 0) : Dense ((momDomain m : Set (Lp ℂ 2 (volume : Measure W))))
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.momDomain_dense`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.momDomain_dense
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
open BookProof.NsFieldMomentumInverse



open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem BookProof.NsFieldMomentumInverse.momDomain_dense {m : W} (hm : m ≠ 0) :
    Dense ((momDomain m : Set (Lp ℂ 2 (volume : Measure W)))) := by sorry
