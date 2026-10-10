-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_contDiff_polyPhase
-- name    : BookProof.MixedLinearEsa.contDiff_polyPhase
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:52.270238+00:00
-- url     : https://prove2.me/theorems/fd6d04c6-b0ed-4442-9d41-b73c2f06b6ad
-- title:
--   `BookProof.MixedLinearEsa.contDiff_polyPhase` (c : ℕ → ℝ) (n : ℕ) (m : V) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyPhase c n m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.contDiff_polyPhase` (c : ℕ → ℝ) (n : ℕ) (m : V) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyPhase c n m)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.contDiff_polyPhase`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.contDiff_polyPhase
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

theorem BookProof.MixedLinearEsa.contDiff_polyPhase (c : ℕ → ℝ) (n : ℕ) (m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyPhase c n m) := by sorry
