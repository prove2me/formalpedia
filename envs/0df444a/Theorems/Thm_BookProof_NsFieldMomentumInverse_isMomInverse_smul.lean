-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_isMomInverse_smul
-- name    : BookProof.NsFieldMomentumInverse.isMomInverse_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:15.618914+00:00
-- url     : https://prove2.me/theorems/228881fd-b0fe-4474-a078-ef7a0a0cbc9d
-- title:
--   `BookProof.NsFieldMomentumInverse.isMomInverse_smul` {m : W} (c : ℂ) {f g : Lp ℂ 2 (volume : Measure W)} (h : IsMomInverse m f g) : IsMomInverse m (c • f) (c • g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.isMomInverse_smul` {m : W} (c : ℂ) {f g : Lp ℂ 2 (volume : Measure W)} (h : IsMomInverse m f g) : IsMomInverse m (c • f) (c • g)
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.isMomInverse_smul`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.isMomInverse_smul
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

theorem BookProof.NsFieldMomentumInverse.isMomInverse_smul {m : W} (c : ℂ) {f g : Lp ℂ 2 (volume : Measure W)}
    (h : IsMomInverse m f g) : IsMomInverse m (c • f) (c • g) := by sorry
