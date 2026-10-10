-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_scalarFibreOp
-- name    : BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:01.041428+00:00
-- url     : https://prove2.me/theorems/9139c5da-5b8e-4b49-b7be-8cf4ce2c7d8a
-- title:
--   `BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : nsScalarFourier V W (scalarFibreOp V T g) = scalarFibreOp V T (nsScalarFourier V W g)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
import Definitions.Def_ChapterNsScalarVectorCurry
import Mathlib
import Definitions.Def_ChapterNsScalarFourier
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier
open BookProof.NsScalarFourier


open MeasureTheory


open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
    (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W (scalarFibreOp V T g) = scalarFibreOp V T (nsScalarFourier V W g) := by sorry
