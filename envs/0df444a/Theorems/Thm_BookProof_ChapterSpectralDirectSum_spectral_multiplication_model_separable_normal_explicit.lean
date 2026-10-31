-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_separable_normal_explicit
-- name    : BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable_normal_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:50.84315+00:00
-- url     : https://prove2.me/theorems/7975db95-4961-4218-a5e8-3fa0947cc440
-- title:
--   Spectral theorem, multiplication-model form, separably valued
-- statement:
--   Let $T$ be a bounded normal operator on a separable complex Hilbert space $H$.  Then $H$ is a Hilbert sum of multiplication models over a **countable** index set:
--   $$H \cong \bigoplus_{x \in S} L^{2}\big(\sigma(T), \mu_{x}\big), \qquad S \text{ countable},$$
--   with $T$ acting as multiplication by the coordinate function on each summand and every $\mu_x$ a probability measure on the spectrum.
--
--   Countability of $S$ is what one gains from separability, and it is what makes the multiplication model usable in the classification arguments, where a spectral measure has to be handled one summand at a time.
--
--   Corrected statement of the retired node `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable`; the normality hypothesis is now an explicit binder, so the target no longer ranges over all bounded operators.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSpectralDirectSum.lean

-- Corrected statement of BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterSpectralDirectSum.lean (Lean 4.28) and timepiece331/BookProof/ChapterSpectralDirectSum.lean (Lean 4.33.1).
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
open BookProof.ChapterSpectralDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

theorem BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable_normal_explicit (hT : IsStarNormal T) [TopologicalSpace.SeparableSpace H] : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), S.Countable ∧ (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ (x : S) (u : Lp ℂ 2 (mu x)), V x (mulRep (mu x) (coordFn T) u) = T (V x u)) := by sorry
