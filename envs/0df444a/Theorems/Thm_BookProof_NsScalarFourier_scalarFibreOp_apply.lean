-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_scalarFibreOp_apply
-- name    : BookProof.NsScalarFourier.scalarFibreOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:06:44.235912+00:00
-- url     : https://prove2.me/theorems/3271e07d-988d-402f-9afb-22a9548fb57c
-- title:
--   `BookProof.NsScalarFourier.scalarFibreOp_apply` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.scalarFibreOp_apply` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : scalarFibreOp V T g = curryLI (fibreOp V T (curryLI.symm g))
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.scalarFibreOp_apply`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.scalarFibreOp_apply
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

theorem BookProof.NsScalarFourier.scalarFibreOp_apply (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    scalarFibreOp V T g = curryLI (fibreOp V T (curryLI.symm g)) := by sorry
