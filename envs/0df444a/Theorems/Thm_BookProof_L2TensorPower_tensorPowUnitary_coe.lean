-- Prove2me | Theorems.Thm_BookProof_L2TensorPower_tensorPowUnitary_coe
-- name    : BookProof.L2TensorPower.tensorPowUnitary_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:28:05.571457+00:00
-- url     : https://prove2.me/theorems/4abe9c96-04a8-4ace-888b-d8bcbe4fca4f
-- title:
--   `BookProof.L2TensorPower.tensorPowUnitary_coe` (n : ℕ) (x : ((L2Space μ).pow n).carrier) : tensorPowUnitary μ n (x : fockSector (L2Space μ) n) = embPow μ n x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterL2TensorPowerUnitary`.
--
--   `BookProof.L2TensorPower.tensorPowUnitary_coe` (n : ℕ) (x : ((L2Space μ).pow n).carrier) : tensorPowUnitary μ n (x : fockSector (L2Space μ) n) = embPow μ n x
--
--   Formalization note: Lean 4 identifier `BookProof.L2TensorPower.tensorPowUnitary_coe`.

-- Generated from ChapterL2TensorPowerUnitary.lean — theorem BookProof.L2TensorPower.tensorPowUnitary_coe
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Mathlib
import Definitions.Def_ChapterL2TensorPowerUnitary
import Definitions.Def_ChapterNsScalarFourier
import Definitions.Def_ChapterScalarDGammaEsa



open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct

noncomputable section


variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

theorem BookProof.L2TensorPower.tensorPowUnitary_coe (n : ℕ) (x : ((L2Space μ).pow n).carrier) :
    tensorPowUnitary μ n (x : fockSector (L2Space μ) n) = embPow μ n x := by sorry
