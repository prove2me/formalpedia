-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_deficiencyTrivialAt_of_real_symbol
-- name    : BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:23.3491+00:00
-- url     : https://prove2.me/theorems/3eefcdcd-85b5-41d7-8f3e-21bb585f3e7a
-- title:
--   `BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol` (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ) (hP : ∀ (f : 𝓢(V, ℂ)) (x : V), (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x) (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) {z : ℂ} (hz : z.im ≠ 0) : BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 P) z
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol
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

theorem BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x)
    (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 P) z := by sorry
