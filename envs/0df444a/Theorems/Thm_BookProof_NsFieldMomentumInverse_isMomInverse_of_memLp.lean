-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_isMomInverse_of_memLp
-- name    : BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:53:16.208353+00:00
-- url     : https://prove2.me/theorems/772716c2-d025-47cd-83f2-b6e3f78961a6
-- title:
--   `BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp` {m : W} (hm : m ≠ 0) (f : Lp ℂ 2 (volume : Measure W)) (hf : MemLp (fun ξ => (f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) 2 (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp` {m : W} (hm : m ≠ 0) (f : Lp ℂ 2 (volume : Measure W)) (hf : MemLp (fun ξ => (f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) 2 (volume : Measure W)) : IsMomInverse m f hf.toLp
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
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

theorem BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp {m : W} (hm : m ≠ 0) (f : Lp ℂ 2 (volume : Measure W))
    (hf : MemLp (fun ξ => (f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) 2 (volume : Measure W)) :
    IsMomInverse m f hf.toLp := by sorry
