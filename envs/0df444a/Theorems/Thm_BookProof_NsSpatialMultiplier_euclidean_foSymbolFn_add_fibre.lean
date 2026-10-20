-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_euclidean_foSymbolFn_add_fibre
-- name    : BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:43:18.013318+00:00
-- url     : https://prove2.me/theorems/7389a207-6a8c-4249-aaa1-28f1046cc8f6
-- title:
--   `BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre` {n : ℕ} (c : ι → ℝ) (s : ι → Fin n) (j : Fin n) (hj : ∀ i, s i ≠ j) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : foSymbol
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre` {n : ℕ} (c : ι → ℝ) (s : ι → Fin n) (j : Fin n) (hj : ∀ i, s i ≠ j) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ)) (x + t • EuclideanSpace.single j (1 : ℝ)) = foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
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

theorem BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre {n : ℕ} (c : ι → ℝ) (s : ι → Fin n) (j : Fin n)
    (hj : ∀ i, s i ≠ j) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ))
        (x + t • EuclideanSpace.single j (1 : ℝ))
      = foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ)) x := by sorry
