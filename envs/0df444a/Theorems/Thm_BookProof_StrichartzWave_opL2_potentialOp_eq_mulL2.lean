-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_opL2_potentialOp_eq_mulL2
-- name    : BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:24.704986+00:00
-- url     : https://prove2.me/theorems/6105c7b2-364d-41da-94e8-b6b5910c7f66
-- title:
--   `BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) : opL2 (po
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) : opL2 (potentialOp W) = (mulL2 (hmem.toLp _)).toLinearMap ∘ₗ (schwartzDomain V).subtype
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2 (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) :
    opL2 (potentialOp W)
      = (mulL2 (hmem.toLp _)).toLinearMap ∘ₗ (schwartzDomain V).subtype := by sorry
