-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_contDiff_mixedSymbolFn
-- name    : BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:20.472992+00:00
-- url     : https://prove2.me/theorems/ed1b23a3-dea1-4495-baf5-ab9fa5f5ff34
-- title:
--   `BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mixedSymbolFn a c w κ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mixedSymbolFn a c w κ)
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.contDiff_mixedSymbolFn (a c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mixedSymbolFn a c w κ) := by sorry
