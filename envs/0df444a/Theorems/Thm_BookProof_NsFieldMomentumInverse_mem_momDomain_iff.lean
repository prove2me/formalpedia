-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_mem_momDomain_iff
-- name    : BookProof.NsFieldMomentumInverse.mem_momDomain_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:53:29.754604+00:00
-- url     : https://prove2.me/theorems/56350c21-cd2a-44a8-9071-579d35f23da5
-- title:
--   `BookProof.NsFieldMomentumInverse.mem_momDomain_iff` {m : W} (f : Lp ℂ 2 (volume : Measure W)) : f ∈ momDomain m ↔ ∃ g, IsMomInverse m f g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.mem_momDomain_iff` {m : W} (f : Lp ℂ 2 (volume : Measure W)) : f ∈ momDomain m ↔ ∃ g, IsMomInverse m f g
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.mem_momDomain_iff`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.mem_momDomain_iff
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

theorem BookProof.NsFieldMomentumInverse.mem_momDomain_iff {m : W} (f : Lp ℂ 2 (volume : Measure W)) :
    f ∈ momDomain m ↔ ∃ g, IsMomInverse m f g := by sorry
