-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_contDiff_foSymbolFn
-- name    : BookProof.FourierMultiplierEsa.contDiff_foSymbolFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:04.235709+00:00
-- url     : https://prove2.me/theorems/109b310c-c2d3-44d0-a19b-721327509b21
-- title:
--   `BookProof.FourierMultiplierEsa.contDiff_foSymbolFn` (c : ι → ℝ) (w : ι → V) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (foSymbolFn c w)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.contDiff_foSymbolFn` (c : ι → ℝ) (w : ι → V) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (foSymbolFn c w)
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.contDiff_foSymbolFn`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.contDiff_foSymbolFn
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.FourierMultiplierEsa.contDiff_foSymbolFn (c : ι → ℝ) (w : ι → V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (foSymbolFn c w) := by sorry
