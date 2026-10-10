-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_norm_gaugeFun
-- name    : BookProof.MixedLinearEsa.norm_gaugeFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:06:26.192992+00:00
-- url     : https://prove2.me/theorems/6fc6c391-c3bb-4473-8e58-d8b30572d8bc
-- title:
--   `BookProof.MixedLinearEsa.norm_gaugeFun` (b m : V) (x : V) : ‖gaugeFun b m x‖ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.norm_gaugeFun` (b m : V) (x : V) : ‖gaugeFun b m x‖ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.norm_gaugeFun`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.norm_gaugeFun
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

theorem BookProof.MixedLinearEsa.norm_gaugeFun (b m : V) (x : V) : ‖gaugeFun b m x‖ = 1 := by sorry
