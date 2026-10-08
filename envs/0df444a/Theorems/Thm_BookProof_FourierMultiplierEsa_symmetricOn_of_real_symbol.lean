-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_symmetricOn_of_real_symbol
-- name    : BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:22:08.814985+00:00
-- url     : https://prove2.me/theorems/a09207e7-3a1c-4651-ad1b-f6b307d02475
-- title:
--   `BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 P)
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 P) := by sorry
