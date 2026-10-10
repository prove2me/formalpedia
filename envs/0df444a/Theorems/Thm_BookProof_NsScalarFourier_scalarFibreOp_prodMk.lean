-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_scalarFibreOp_prodMk
-- name    : BookProof.NsScalarFourier.scalarFibreOp_prodMk
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:11:52.577775+00:00
-- url     : https://prove2.me/theorems/0df58894-1ace-48ec-9bd7-f301f32233de
-- title:
--   `BookProof.NsScalarFourier.scalarFibreOp_prodMk` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.scalarFibreOp_prodMk` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) : scalarFibreOp V T (prodMk a c) = prodMk a (T c)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.scalarFibreOp_prodMk`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.scalarFibreOp_prodMk
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

theorem BookProof.NsScalarFourier.scalarFibreOp_prodMk (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
    scalarFibreOp V T (prodMk a c) = prodMk a (T c) := by sorry
