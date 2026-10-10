-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_polyPotential_add_momentum_essentiallySelfAdjoint
-- name    : BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:08:25.33737+00:00
-- url     : https://prove2.me/theorems/770384ce-0d14-42f9-9f9f-9e7854f98cf4
-- title:
--   `BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint` (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint` (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp (polyPotential c n m) m))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint
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

theorem BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint (c : ℕ → ℝ) (n : ℕ) {m : V}
    (hm : m ≠ 0) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp (polyPotential c n m) m)) := by sorry
