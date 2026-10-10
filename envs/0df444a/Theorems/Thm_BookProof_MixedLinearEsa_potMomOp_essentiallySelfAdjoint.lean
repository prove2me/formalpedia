-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_essentiallySelfAdjoint
-- name    : BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:28.956988+00:00
-- url     : https://prove2.me/theorems/04a7e356-9d6e-4972-9c90-c3843f62a341
-- title:
--   `BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint` {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W) {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (hθd : ∀ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint` {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W) {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp W m))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.potMomOp_essentiallySelfAdjoint {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W)
    {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp W m)) := by sorry
