-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_deficiencyTrivialAt
-- name    : BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:21.935159+00:00
-- url     : https://prove2.me/theorems/47d0e1c2-0f52-4411-af30-8cf02612b0e6
-- title:
--   `BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt` {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W) {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (hθd : ∀ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt` {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W) {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (schwartzDomain V) (opL2 (potMomOp W m)) z
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.FourierMultiplierEsa
open BookProof.ShiftedHermiteCore
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W)
    {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (potMomOp W m)) z := by sorry
