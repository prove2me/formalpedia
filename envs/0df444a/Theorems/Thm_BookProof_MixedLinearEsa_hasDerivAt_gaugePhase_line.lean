-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_gaugePhase_line
-- name    : BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:05:58.763536+00:00
-- url     : https://prove2.me/theorems/a135c96b-d1c7-4ba3-9f8d-ee6ac412f95c
-- title:
--   `BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line` (b m : V) (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-(inner ℝ x b : ℝ)) 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line` (b m : V) (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-(inner ℝ x b : ℝ)) 0
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-(inner ℝ x b : ℝ)) 0 := by sorry
