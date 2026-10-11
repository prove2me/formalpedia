-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_multiplierOp_apply_eq
-- name    : BookProof.StrichartzWave.multiplierOp_apply_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:28.068884+00:00
-- url     : https://prove2.me/theorems/3038f9f0-1fd6-46fc-8c21-e59fa90042b0
-- title:
--   `BookProof.StrichartzWave.multiplierOp_apply_eq` (m : V → ℝ) (f : 𝓢(V, ℂ)) : (multiplierOp m f : 𝓢(V, ℂ)) = 𝓕⁻ (potentialOp m (𝓕 f : 𝓢(V, ℂ)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.multiplierOp_apply_eq` (m : V → ℝ) (f : 𝓢(V, ℂ)) : (multiplierOp m f : 𝓢(V, ℂ)) = 𝓕⁻ (potentialOp m (𝓕 f : 𝓢(V, ℂ)))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.multiplierOp_apply_eq`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.multiplierOp_apply_eq
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.multiplierOp_apply_eq (m : V → ℝ) (f : 𝓢(V, ℂ)) :
    (multiplierOp m f : 𝓢(V, ℂ)) = 𝓕⁻ (potentialOp m (𝓕 f : 𝓢(V, ℂ))) := by sorry
