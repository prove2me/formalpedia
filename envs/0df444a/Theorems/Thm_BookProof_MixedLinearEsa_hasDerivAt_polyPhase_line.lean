-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_polyPhase_line
-- name    : BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:08:02.159987+00:00
-- url     : https://prove2.me/theorems/4245a288-eb33-4549-81f8-9a01bcafcba2
-- title:
--   `BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line` (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => polyPhase c n m (x + t • m)) (-(polyPotential c n m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line` (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) (x : V) : HasDerivAt (fun t : ℝ => polyPhase c n m (x + t • m)) (-(polyPotential c n m x)) 0
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line
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

theorem BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => polyPhase c n m (x + t • m)) (-(polyPotential c n m x)) 0 := by sorry
