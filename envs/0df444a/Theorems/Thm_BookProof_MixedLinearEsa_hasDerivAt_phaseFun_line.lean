-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_phaseFun_line
-- name    : BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:01.54346+00:00
-- url     : https://prove2.me/theorems/c4296856-694b-4c95-b3ef-f433f619ac60
-- title:
--   `BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line` {W θ : V → ℝ} {m : V} (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) (x : V) : HasDerivAt (fun t : ℝ => phaseFu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line` {W θ : V → ℝ} {m : V} (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) (x : V) : HasDerivAt (fun t : ℝ => phaseFun θ (x + t • m)) (phaseFun θ x * (Complex.I * ((-(W x) : ℝ) : ℂ))) 0
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line
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

theorem BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line {W θ : V → ℝ} {m : V}
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) (x : V) :
    HasDerivAt (fun t : ℝ => phaseFun θ (x + t • m))
      (phaseFun θ x * (Complex.I * ((-(W x) : ℝ) : ℂ))) 0 := by sorry
