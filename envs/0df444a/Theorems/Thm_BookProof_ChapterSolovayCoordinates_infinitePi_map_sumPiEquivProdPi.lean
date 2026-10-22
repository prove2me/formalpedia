-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_infinitePi_map_sumPiEquivProdPi
-- name    : BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:52:34.540384+00:00
-- url     : https://prove2.me/theorems/de192171-ed8e-44bc-b75a-f80f8e856017
-- title:
--   `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi` {ι ι' : Type*} [Fintype ι] {X : ι ⊕ ι' → Type*} [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i)) [∀ i, I
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi` {ι ι' : Type*} [Fintype ι] {X : ι ⊕ ι' → Type*} [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)] : Measure.map (MeasurableEquiv.sumPiEquivProdPi X) (Measure.infinitePi mu) = (Measure.pi fun i : ι => mu (Sum.inl i)).prod (Measure.infinitePi fun j : ι' => mu (Sum.inr j))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi {ι ι' : Type*} [Fintype ι] {X : ι ⊕ ι' → Type*}
    [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] :
    Measure.map (MeasurableEquiv.sumPiEquivProdPi X) (Measure.infinitePi mu)
      = (Measure.pi fun i : ι => mu (Sum.inl i)).prod
        (Measure.infinitePi fun j : ι' => mu (Sum.inr j)) := by sorry
