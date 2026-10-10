-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_cut_mem_momDomain
-- name    : BookProof.NsFieldMomentumInverse.cut_mem_momDomain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:53:31.552033+00:00
-- url     : https://prove2.me/theorems/025c9bee-8b29-413e-a276-092739c95776
-- title:
--   `BookProof.NsFieldMomentumInverse.cut_mem_momDomain` {m : W} (hm : m ≠ 0) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : cut m n f ∈ momDomain m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.cut_mem_momDomain` {m : W} (hm : m ≠ 0) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : cut m n f ∈ momDomain m
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.cut_mem_momDomain`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.cut_mem_momDomain
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

theorem BookProof.NsFieldMomentumInverse.cut_mem_momDomain {m : W} (hm : m ≠ 0) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) :
    cut m n f ∈ momDomain m := by sorry
