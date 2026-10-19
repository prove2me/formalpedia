-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_isMomInverse_momentumOp
-- name    : BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:31.100572+00:00
-- url     : https://prove2.me/theorems/d7fd7314-2a33-4732-b1d5-f5181b112f71
-- title:
--   `BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp` (m : W) (f : 𝓢(W, ℂ)) : IsMomInverse m (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f))) (l2Fourier W (f.toLp 2 (vo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp` (m : W) (f : 𝓢(W, ℂ)) : IsMomInverse m (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f))) (l2Fourier W (f.toLp 2 (volume : Measure W)))
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterStrichartzWave
open BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.NsSpatialMultiplier
open BookProof.StrichartzWave
open BookProof.NsFieldMomentumInverse



open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp (m : W) (f : 𝓢(W, ℂ)) :
    IsMomInverse m (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f)))
      (l2Fourier W (f.toLp 2 (volume : Measure W))) := by sorry
