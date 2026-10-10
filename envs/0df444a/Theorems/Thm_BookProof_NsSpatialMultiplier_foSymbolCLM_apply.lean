-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_foSymbolCLM_apply
-- name    : BookProof.NsSpatialMultiplier.foSymbolCLM_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:40.678974+00:00
-- url     : https://prove2.me/theorems/45617e1c-eb71-432c-a065-b6200379c04c
-- title:
--   `BookProof.NsSpatialMultiplier.foSymbolCLM_apply` (c : ι → ℝ) (w : ι → V) (x : V) : foSymbolCLM c w x = foSymbolFn c w x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.foSymbolCLM_apply` (c : ι → ℝ) (w : ι → V) (x : V) : foSymbolCLM c w x = foSymbolFn c w x
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.foSymbolCLM_apply`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.foSymbolCLM_apply
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

theorem BookProof.NsSpatialMultiplier.foSymbolCLM_apply (c : ι → ℝ) (w : ι → V) (x : V) :
    foSymbolCLM c w x = foSymbolFn c w x := by sorry
