-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_exists_probabilityMeasure_of_state_of_positive_explicit
-- name    : BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_of_positive_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:48.857136+00:00
-- url     : https://prove2.me/theorems/1fe6ec5d-02a6-49d7-bf1b-aec0e5a1da1b
-- title:
--   Every positive normalised functional on $C(X)$ is a probability measure
-- statement:
--   Let $\psi$ be a linear functional on $C(X)$ that is positive ($\psi(g^{*}g) \ge 0$ for all $g$) and normalised ($\psi(1) = 1$).  Then there is a probability measure $\mu$ on $X$ with
--   $$\psi(g) = \int_{X} g \, d\mu \qquad \text{for every } g \in C(X).$$
--
--   This is the Riesz–Markov representation theorem in the form the Gelfand model needs: states of the commutative $C^{*}$-algebra $C(X)$ *are* probability measures.  Positivity is what makes the representing measure non-negative, and normalisation what makes it a probability.
--
--   Corrected statement of the retired node `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state`; the positivity hypothesis `hpos` is now an explicit binder rather than a section variable the export dropped.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterAbelianGelfandModel.lean

-- Corrected statement of BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterAbelianGelfandModel.lean (Lean 4.28) and timepiece331/BookProof/ChapterAbelianGelfandModel.lean (Lean 4.33.1).
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianGelfandModel


open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

theorem BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_of_positive_explicit (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g)) (hone : psi 1 = 1) : ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu := by sorry
