-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_foSymbolFn_add_fibre
-- name    : BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:59.571597+00:00
-- url     : https://prove2.me/theorems/45edef17-359c-4d1e-9071-5aaf319a64dd
-- title:
--   `BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre` (c : ι → ℝ) (w : ι → V) (x m : V) (hm : ∀ i, (inner ℝ m (w i) : ℝ) = 0) (t : ℝ) : foSymbolFn c w (x + t • m) = foSymbolFn c w x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre` (c : ι → ℝ) (w : ι → V) (x m : V) (hm : ∀ i, (inner ℝ m (w i) : ℝ) = 0) (t : ℝ) : foSymbolFn c w (x + t • m) = foSymbolFn c w x
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
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

theorem BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre (c : ι → ℝ) (w : ι → V) (x m : V)
    (hm : ∀ i, (inner ℝ m (w i) : ℝ) = 0) (t : ℝ) :
    foSymbolFn c w (x + t • m) = foSymbolFn c w x := by sorry
