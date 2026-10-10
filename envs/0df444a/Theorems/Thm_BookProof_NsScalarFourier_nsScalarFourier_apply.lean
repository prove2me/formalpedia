-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_apply
-- name    : BookProof.NsScalarFourier.nsScalarFourier_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:56.316883+00:00
-- url     : https://prove2.me/theorems/d8efc4b9-e016-4859-b5bb-be06e3890e7d
-- title:
--   `BookProof.NsScalarFourier.nsScalarFourier_apply` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : nsScalarFourier V W g = curryLI (nsPartialFourier V W (curryLI.sym
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.nsScalarFourier_apply` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : nsScalarFourier V W g = curryLI (nsPartialFourier V W (curryLI.symm g))
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.nsScalarFourier_apply`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.nsScalarFourier_apply
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

variable (V W) in

theorem BookProof.NsScalarFourier.nsScalarFourier_apply (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W g = curryLI (nsPartialFourier V W (curryLI.symm g)) := by sorry
