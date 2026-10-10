-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_symmetric
-- name    : BookProof.MixedLinearEsa.potMomOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:10.955297+00:00
-- url     : https://prove2.me/theorems/1daca117-8227-48a8-9822-3b63f2c61705
-- title:
--   `BookProof.MixedLinearEsa.potMomOp_symmetric` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (m : V) : SymmetricOn (schwartzDomain V) (opL2 (potMomOp W m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.potMomOp_symmetric` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (m : V) : SymmetricOn (schwartzDomain V) (opL2 (potMomOp W m))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.potMomOp_symmetric`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.potMomOp_symmetric
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveUnboundedPotential
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.potMomOp_symmetric (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (m : V) :
    SymmetricOn (schwartzDomain V) (opL2 (potMomOp W m)) := by sorry
