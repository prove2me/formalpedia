-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasCompactSupport_cutSchwartz
-- name    : BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:04:47.667975+00:00
-- url     : https://prove2.me/theorems/b9cc3dff-87ed-4757-be3c-91ea425783f5
-- title:
--   `BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz` (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz` (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) : HasCompactSupport ((cutSchwartz g hg hgcs f : V → ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) :
    HasCompactSupport ((cutSchwartz g hg hgcs f : V → ℂ)) := by sorry
