-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_momSymbol_ne_zero_ae
-- name    : BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:57.417209+00:00
-- url     : https://prove2.me/theorems/72d1b90c-6ba9-4497-b47b-3bc09c203388
-- title:
--   `BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae` {m : W} (hm : m ≠ 0) : ∀ᵐ ξ ∂(volume : Measure W), momSymbol m ξ ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae` {m : W} (hm : m ≠ 0) : ∀ᵐ ξ ∂(volume : Measure W), momSymbol m ξ ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
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

theorem BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae {m : W} (hm : m ≠ 0) :
    ∀ᵐ ξ ∂(volume : Measure W), momSymbol m ξ ≠ 0 := by sorry
