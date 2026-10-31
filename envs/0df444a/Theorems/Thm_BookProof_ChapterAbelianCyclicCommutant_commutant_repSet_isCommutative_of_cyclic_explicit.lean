-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutant_repSet_isCommutative_of_cyclic_explicit
-- name    : BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_of_cyclic_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:46.645875+00:00
-- url     : https://prove2.me/theorems/610583c2-2d8e-4545-9859-7a7ad572dc43
-- title:
--   A cyclic representation has a commutative commutant
-- statement:
--   Let $\pi$ be a representation of $C(X)$ on a Hilbert space $H$ with a cyclic vector $\xi$, i.e. $\mathrm{repVec}(\pi,\xi)$ has dense range.  Then the commutant of $\pi$ is commutative: for any two operators $S, R$ that commute with every $\pi(g)$,
--   $$S R = R S .$$
--
--   The argument is the standard one: on the dense set of vectors $\pi(g)\xi$ both products agree, and density plus boundedness extend the identity to $H$.  Cyclicity is indispensable — a non-cyclic representation has a commutant as large as the bounded operators of a multiplicity space.
--
--   Corrected statement of the retired node `BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative`: the cyclicity hypothesis `hcyc` was a section variable not occurring in the type and was dropped by the export; it is an explicit binder here.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterAbelianCyclicCommutant.lean

-- Corrected statement of BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterAbelianCyclicCommutant.lean (Lean 4.28) and timepiece331/BookProof/ChapterAbelianCyclicCommutant.lean (Lean 4.33.1).
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
open BookProof.ChapterAbelianCyclicCommutant


noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

theorem BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_of_cyclic_explicit (hcyc : DenseRange (repVec pi xi)) {S R : H →L[ℂ] H} (hS : S ∈ (repSet pi).centralizer) (hR : R ∈ (repSet pi).centralizer) : S * R = R * S := by sorry
