-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_fourier_opL2_momentumOp
-- name    : BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:50.782001+00:00
-- url     : https://prove2.me/theorems/2afbbc3f-e270-49db-98f7-4dd150da297c
-- title:
--   `BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp` (m : V) (f : 𝓢(V, ℂ)) : l2Fourier V (opL2 (momentumOp m) (schwartzEquiv V f)) = (mulSymbolOp (fun x => 2 * Real.pi * (inner
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp` (m : V) (f : 𝓢(V, ℂ)) : l2Fourier V (opL2 (momentumOp m) (schwartzEquiv V f)) = (mulSymbolOp (fun x => 2 * Real.pi * (inner ℝ x m : ℝ)) (𝓕 f)).toLp 2 (volume : Measure V)
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

theorem BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp (m : V) (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 (momentumOp m) (schwartzEquiv V f))
      = (mulSymbolOp (fun x => 2 * Real.pi * (inner ℝ x m : ℝ)) (𝓕 f)).toLp
          2 (volume : Measure V) := by sorry
