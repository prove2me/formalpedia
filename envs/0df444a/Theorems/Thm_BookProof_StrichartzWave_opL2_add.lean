-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_opL2_add
-- name    : BookProof.StrichartzWave.opL2_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:10.197157+00:00
-- url     : https://prove2.me/theorems/11343f68-1647-416f-aea4-df98913c9a06
-- title:
--   `BookProof.StrichartzWave.opL2_add` (T S : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) : opL2 (T + S) = opL2 T + opL2 S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.opL2_add` (T S : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) : opL2 (T + S) = opL2 T + opL2 S
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.opL2_add`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.opL2_add
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.opL2_add (T S : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) : opL2 (T + S) = opL2 T + opL2 S := by sorry
