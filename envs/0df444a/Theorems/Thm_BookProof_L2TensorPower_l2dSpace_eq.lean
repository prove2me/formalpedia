-- Prove2me | Theorems.Thm_BookProof_L2TensorPower_l2dSpace_eq
-- name    : BookProof.L2TensorPower.l2dSpace_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:29:29.377855+00:00
-- url     : https://prove2.me/theorems/2f19a83b-ab39-47ba-b7e3-1fbf23f8ea83
-- title:
--   `BookProof.L2TensorPower.l2dSpace_eq` (d : ℕ) : BookProof.YangMillsNonAbelianEsa.L2dSpace d = L2Space (volume : Measure (Vd d))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterL2TensorPowerUnitary`.
--
--   `BookProof.L2TensorPower.l2dSpace_eq` (d : ℕ) : BookProof.YangMillsNonAbelianEsa.L2dSpace d = L2Space (volume : Measure (Vd d))
--
--   Formalization note: Lean 4 identifier `BookProof.L2TensorPower.l2dSpace_eq`.

-- Generated from ChapterL2TensorPowerUnitary.lean — theorem BookProof.L2TensorPower.l2dSpace_eq
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Mathlib
import Definitions.Def_ChapterL2TensorPowerUnitary
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.TensorCore



open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct

noncomputable section


variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

theorem BookProof.L2TensorPower.l2dSpace_eq (d : ℕ) :
    BookProof.YangMillsNonAbelianEsa.L2dSpace d = L2Space (volume : Measure (Vd d)) := by sorry
