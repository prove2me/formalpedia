-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_fibreOp_fibMk
-- name    : BookProof.NsScalarFourier.fibreOp_fibMk
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:23.570488+00:00
-- url     : https://prove2.me/theorems/32e9f55a-4016-4050-be76-067916e27261
-- title:
--   `BookProof.NsScalarFourier.fibreOp_fibMk` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.fibreOp_fibMk` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) : fibreOp V T (fibMk a c) = fibMk a (T c)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.fibreOp_fibMk`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.fibreOp_fibMk
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

theorem BookProof.NsScalarFourier.fibreOp_fibMk (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
    fibreOp V T (fibMk a c) = fibMk a (T c) := by sorry
