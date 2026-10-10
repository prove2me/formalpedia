-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_prodMk_eq
-- name    : BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:50.199377+00:00
-- url     : https://prove2.me/theorems/008f5ce6-3cee-4a46-ade0-92821a00afb4
-- title:
--   `BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq` (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) : nsScalarFourier V W (prodMk a c) = curryLI (nsPartialFou
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq` (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) : nsScalarFourier V W (prodMk a c) = curryLI (nsPartialFourier V W (fibMk a c))
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq
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

theorem BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq (a : Lp ℂ 2 (volume : Measure V))
    (c : Lp ℂ 2 (volume : Measure W)) :
    nsScalarFourier V W (prodMk a c) = curryLI (nsPartialFourier V W (fibMk a c)) := by sorry
