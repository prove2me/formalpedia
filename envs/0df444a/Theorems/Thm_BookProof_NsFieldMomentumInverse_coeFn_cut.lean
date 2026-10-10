-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_coeFn_cut
-- name    : BookProof.NsFieldMomentumInverse.coeFn_cut
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:53:34.447528+00:00
-- url     : https://prove2.me/theorems/f1806b72-1314-4304-b103-f75909858a95
-- title:
--   `BookProof.NsFieldMomentumInverse.coeFn_cut` (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : (cut m n f : W → ℂ) =ᵐ[(volume : Measure W)] (cutSet m n).indicator (f : W → ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.coeFn_cut` (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : (cut m n f : W → ℂ) =ᵐ[(volume : Measure W)] (cutSet m n).indicator (f : W → ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.coeFn_cut`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.coeFn_cut
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

theorem BookProof.NsFieldMomentumInverse.coeFn_cut (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) :
    (cut m n f : W → ℂ) =ᵐ[(volume : Measure W)] (cutSet m n).indicator (f : W → ℂ) := by sorry
