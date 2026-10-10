-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_gaugeFun_line
-- name    : BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:05:31.287292+00:00
-- url     : https://prove2.me/theorems/395fa1c3-2a21-4e46-9958-296497189b96
-- title:
--   `BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line` (b m : V) (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m)) (gaugeFun b m x * (Complex.I * ((-(inner ℝ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line` (b m : V) (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m)) (gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) 0
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line
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


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m))
      (gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) 0 := by sorry
