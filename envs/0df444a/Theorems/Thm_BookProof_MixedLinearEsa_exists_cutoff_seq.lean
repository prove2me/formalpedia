-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_exists_cutoff_seq
-- name    : BookProof.MixedLinearEsa.exists_cutoff_seq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:04:51.008771+00:00
-- url     : https://prove2.me/theorems/b45a138e-92c0-426e-9891-07e872788fca
-- title:
--   `BookProof.MixedLinearEsa.exists_cutoff_seq` : ∃ (cut : ℕ → V → ℝ) (K : ℝ), (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)) ∧ (∀ n, HasCompactSupport (cut n)) ∧...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.exists_cutoff_seq` : ∃ (cut : ℕ → V → ℝ) (K : ℝ), (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)) ∧ (∀ n, HasCompactSupport (cut n)) ∧ (∀ n x, ‖cut n x‖ ≤ 1) ∧ (∀ x : V, ∀ᶠ n in Filter.atTop, cut n x = 1 ∧ fderiv ℝ (cut n) x = 0) ∧ (∀ n x, ‖fderiv ℝ (cut n) x‖ ≤ K)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.exists_cutoff_seq`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.exists_cutoff_seq
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

theorem BookProof.MixedLinearEsa.exists_cutoff_seq :
    ∃ (cut : ℕ → V → ℝ) (K : ℝ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)) ∧
      (∀ n, HasCompactSupport (cut n)) ∧
      (∀ n x, ‖cut n x‖ ≤ 1) ∧
      (∀ x : V, ∀ᶠ n in Filter.atTop, cut n x = 1 ∧ fderiv ℝ (cut n) x = 0) ∧
      (∀ n x, ‖fderiv ℝ (cut n) x‖ ≤ K) := by sorry
