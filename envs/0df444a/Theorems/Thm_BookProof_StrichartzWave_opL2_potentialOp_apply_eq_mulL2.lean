-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_opL2_potentialOp_apply_eq_mulL2
-- name    : BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:20.686513+00:00
-- url     : https://prove2.me/theorems/221e3225-637b-4102-9985-ab686846ed82
-- title:
--   `BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) (f :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) (f : 𝓢(V, ℂ)) : opL2 (potentialOp W) (schwartzEquiv V f) = mulL2 (hmem.toLp _) (f.toLp 2 (volume : Measure V))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.opL2_potentialOp_apply_eq_mulL2 (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) (f : 𝓢(V, ℂ)) :
    opL2 (potentialOp W) (schwartzEquiv V f)
      = mulL2 (hmem.toLp _) (f.toLp 2 (volume : Measure V)) := by sorry
