-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_infinitePi_map_sumPiEquivProdPi_symm
-- name    : BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:53:02.223664+00:00
-- url     : https://prove2.me/theorems/6b0acc77-30d8-471c-8ff6-dfc60bc804f8
-- title:
--   `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm` {ι ι' : Type*} {X : ι ⊕ ι' → Type*} [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i)) [∀ i, IsProbab
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm` {ι ι' : Type*} {X : ι ⊕ ι' → Type*} [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)] : Measure.map (MeasurableEquiv.sumPiEquivProdPi X).symm ((Measure.infinitePi fun i : ι => mu (Sum.inl i)).prod (Measure.infinitePi fun j : ι' => mu (Sum.inr j))) = Measure.infinitePi mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm {ι ι' : Type*} {X : ι ⊕ ι' → Type*}
    [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] :
    Measure.map (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.infinitePi fun i : ι => mu (Sum.inl i)).prod
        (Measure.infinitePi fun j : ι' => mu (Sum.inr j))) = Measure.infinitePi mu := by sorry
