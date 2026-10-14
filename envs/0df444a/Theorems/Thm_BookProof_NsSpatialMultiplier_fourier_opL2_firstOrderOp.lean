-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_fourier_opL2_firstOrderOp
-- name    : BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:43:00.237498+00:00
-- url     : https://prove2.me/theorems/2a5a237e-0410-456b-9b88-f4b94a9073bd
-- title:
--   `BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp` (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) : l2Fourier V (opL2 (firstOrderOp c w) (schwartzEquiv V f)) = (mulSymbolOp (foSymbol
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp` (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) : l2Fourier V (opL2 (firstOrderOp c w) (schwartzEquiv V f)) = (mulSymbolOp (foSymbolFn c w) (𝓕 f)).toLp 2 (volume : Measure V)
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
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

theorem BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 (firstOrderOp c w) (schwartzEquiv V f))
      = (mulSymbolOp (foSymbolFn c w) (𝓕 f)).toLp 2 (volume : Measure V) := by sorry
