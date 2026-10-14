-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_polynomialPotential_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:25.150996+00:00
-- url     : https://prove2.me/theorems/f9e8c237-8358-4567-b4e6-c32cb27274b0
-- title:
--   `BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint` (k : ℕ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potentialOp (fun x : V => ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint` (k : ℕ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potentialOp (fun x : V => ‖x‖ ^ (2 * k))))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint (k : ℕ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (potentialOp (fun x : V => ‖x‖ ^ (2 * k)))) := by sorry
