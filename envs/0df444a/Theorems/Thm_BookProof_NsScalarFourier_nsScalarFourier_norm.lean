-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_norm
-- name    : BookProof.NsScalarFourier.nsScalarFourier_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:11:29.603542+00:00
-- url     : https://prove2.me/theorems/64a411f4-c8b8-44cd-ba1a-35c280686c00
-- title:
--   `BookProof.NsScalarFourier.nsScalarFourier_norm` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : ‖nsScalarFourier V W g‖ = ‖g‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.nsScalarFourier_norm` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : ‖nsScalarFourier V W g‖ = ‖g‖
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.nsScalarFourier_norm`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.nsScalarFourier_norm
import Definitions.Def_ChapterNsPartialFourier
import Definitions.Def_ChapterNsScalarVectorCurry
import Mathlib
import Definitions.Def_ChapterNsScalarFourier
open BookProof.NsScalarFourier


open MeasureTheory


open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable (V W) in

theorem BookProof.NsScalarFourier.nsScalarFourier_norm (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    ‖nsScalarFourier V W g‖ = ‖g‖ := by sorry
