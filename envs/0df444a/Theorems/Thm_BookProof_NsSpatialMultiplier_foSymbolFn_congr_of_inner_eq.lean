-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_foSymbolFn_congr_of_inner_eq
-- name    : BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:12.572383+00:00
-- url     : https://prove2.me/theorems/04dc235f-b1bc-4132-9890-d5f97269ee9e
-- title:
--   `BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq` (c : ι → ℝ) (w : ι → V) {x y : V} (h : ∀ i, (inner ℝ x (w i) : ℝ) = inner ℝ y (w i)) : foSymbolFn c w x = foSymbolFn c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq` (c : ι → ℝ) (w : ι → V) {x y : V} (h : ∀ i, (inner ℝ x (w i) : ℝ) = inner ℝ y (w i)) : foSymbolFn c w x = foSymbolFn c w y
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
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

theorem BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq (c : ι → ℝ) (w : ι → V) {x y : V}
    (h : ∀ i, (inner ℝ x (w i) : ℝ) = inner ℝ y (w i)) :
    foSymbolFn c w x = foSymbolFn c w y := by sorry
