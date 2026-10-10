-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_hasTemperateGrowth_foSymbol
-- name    : BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:01.028389+00:00
-- url     : https://prove2.me/theorems/c826c229-7d36-4a32-9fbb-d079f093d350
-- title:
--   `BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol` (c : ι → ℝ) (w : ι → V) : Function.HasTemperateGrowth (fun x : V => ((foSymbolFn c w x : ℝ) : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol` (c : ι → ℝ) (w : ι → V) : Function.HasTemperateGrowth (fun x : V => ((foSymbolFn c w x : ℝ) : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol (c : ι → ℝ) (w : ι → V) :
    Function.HasTemperateGrowth (fun x : V => ((foSymbolFn c w x : ℝ) : ℂ)) := by sorry
