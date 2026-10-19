-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_general_inc
-- name    : BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:44:30.549996+00:00
-- url     : https://prove2.me/theorems/92aea1ac-94d8-47ed-9d95-34739a8e76bb
-- title:
--   `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc` : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), (∀ x :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc` : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ (x : S) (u : Lp ℂ 2 (mu x)), V x (mulRep (mu x) (coordFn T) u) = T (V x u))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc`.
--
--   Replaces the retired node `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general`, whose stored statement omitted the `hT` hypothesis binder (dropped `include`).

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc
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


include hT in

theorem BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_inc :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (coordFn T) u) = T (V x u)) := by sorry
