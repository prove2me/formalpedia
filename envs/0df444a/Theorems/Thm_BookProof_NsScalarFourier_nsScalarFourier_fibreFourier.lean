-- Prove2me | Theorems.Thm_BookProof_NsScalarFourier_nsScalarFourier_fibreFourier
-- name    : BookProof.NsScalarFourier.nsScalarFourier_fibreFourier
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:45.53898+00:00
-- url     : https://prove2.me/theorems/1a67da25-e773-4255-be36-a7f0ade52bec
-- title:
--   `BookProof.NsScalarFourier.nsScalarFourier_fibreFourier` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : nsScalarFourier V W (scalarFibreOp V (fibreFourierCLM W) g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarFourier`.
--
--   `BookProof.NsScalarFourier.nsScalarFourier_fibreFourier` (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) : nsScalarFourier V W (scalarFibreOp V (fibreFourierCLM W) g) = scalarFibreOp V (fibreFourierCLM W) (nsScalarFourier V W g)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarFourier.nsScalarFourier_fibreFourier`.

-- Generated from ChapterNsScalarFourier.lean — theorem BookProof.NsScalarFourier.nsScalarFourier_fibreFourier
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

theorem BookProof.NsScalarFourier.nsScalarFourier_fibreFourier
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W (scalarFibreOp V (fibreFourierCLM W) g)
      = scalarFibreOp V (fibreFourierCLM W) (nsScalarFourier V W g) := by sorry
