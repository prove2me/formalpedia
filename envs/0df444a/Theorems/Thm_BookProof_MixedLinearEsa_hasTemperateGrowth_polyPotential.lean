-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasTemperateGrowth_polyPotential
-- name    : BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:48.108981+00:00
-- url     : https://prove2.me/theorems/494eb577-cd99-46e1-bd85-b00d5f4c0329
-- title:
--   `BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential` (c : ℕ → ℝ) (n : ℕ) (m : V) : Function.HasTemperateGrowth (polyPotential c n m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential` (c : ℕ → ℝ) (n : ℕ) (m : V) : Function.HasTemperateGrowth (polyPotential c n m)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential
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

theorem BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential (c : ℕ → ℝ) (n : ℕ) (m : V) :
    Function.HasTemperateGrowth (polyPotential c n m) := by sorry
