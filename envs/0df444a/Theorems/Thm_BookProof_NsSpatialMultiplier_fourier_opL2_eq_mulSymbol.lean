-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_fourier_opL2_eq_mulSymbol
-- name    : BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:43:04.701646+00:00
-- url     : https://prove2.me/theorems/5c152ad8-f742-4b4d-adfe-e43623c3b367
-- title:
--   `BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x) (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ))) (f : 𝓢(V, ℂ)) : l2Fourier V (opL2 P (schwartzEquiv V f)) = (mulSymbolOp σ (𝓕 f)).toLp 2 (volume : Measure V)
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol
import Definitions.Def_ChapterFourierMultiplierEsa
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
open BookProof.FarisLavine
open BookProof.StrichartzWave
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

theorem BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x)
    (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ)))
    (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 P (schwartzEquiv V f))
      = (mulSymbolOp σ (𝓕 f)).toLp 2 (volume : Measure V) := by sorry
