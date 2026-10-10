-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_cutSchwartz
-- name    : BookProof.MixedLinearEsa.momentumOp_cutSchwartz
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:04:47.155594+00:00
-- url     : https://prove2.me/theorems/33a78f71-fe04-4db2-ab6d-68a335d783df
-- title:
--   `BookProof.MixedLinearEsa.momentumOp_cutSchwartz` (m : V) (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) (x : V) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.momentumOp_cutSchwartz` (m : V) (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) (x : V) : (momentumOp m (cutSchwartz g hg hgcs f)) x = -Complex.I * (f x * ((fderiv ℝ g x m : ℝ) : ℂ)) + ((g x : ℝ) : ℂ) * (momentumOp m f x)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.momentumOp_cutSchwartz`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.momentumOp_cutSchwartz
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.momentumOp_cutSchwartz (m : V) (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) (x : V) :
    (momentumOp m (cutSchwartz g hg hgcs f)) x
      = -Complex.I * (f x * ((fderiv ℝ g x m : ℝ) : ℂ))
        + ((g x : ℝ) : ℂ) * (momentumOp m f x) := by sorry
