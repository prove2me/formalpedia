-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_mulSymbolOp_apply
-- name    : BookProof.NsSpatialMultiplier.mulSymbolOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:10.616983+00:00
-- url     : https://prove2.me/theorems/80200bf8-8cd8-46fb-af97-ea7dade1b720
-- title:
--   `BookProof.NsSpatialMultiplier.mulSymbolOp_apply` (σ : V → ℝ) (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ))) (f : 𝓢(V, ℂ)) (x : V) : (mulSymbolOp σ f :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.mulSymbolOp_apply` (σ : V → ℝ) (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ))) (f : 𝓢(V, ℂ)) (x : V) : (mulSymbolOp σ f : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * f x
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.mulSymbolOp_apply`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.mulSymbolOp_apply
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFarisLavine
open BookProof.FarisLavine
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.NsSpatialMultiplier.mulSymbolOp_apply (σ : V → ℝ)
    (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ)))
    (f : 𝓢(V, ℂ)) (x : V) :
    (mulSymbolOp σ f : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * f x := by sorry
