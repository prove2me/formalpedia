-- Prove2me | Theorems.Thm_BookProof_L2TensorPower_embPow_succ_tmul
-- name    : BookProof.L2TensorPower.embPow_succ_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:29:58.945204+00:00
-- url     : https://prove2.me/theorems/2dcb2f4d-f5c0-46d6-8cdf-f1573db2af83
-- title:
--   `BookProof.L2TensorPower.embPow_succ_tmul` (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) : embPow μ (n + 1) (a ⊗ₜ[ℂ] t) = splitIso μ n (prodMk a (embPow μ n t))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterL2TensorPowerUnitary`.
--
--   `BookProof.L2TensorPower.embPow_succ_tmul` (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) : embPow μ (n + 1) (a ⊗ₜ[ℂ] t) = splitIso μ n (prodMk a (embPow μ n t))
--
--   Formalization note: Lean 4 identifier `BookProof.L2TensorPower.embPow_succ_tmul`.

-- Generated from ChapterL2TensorPowerUnitary.lean — theorem BookProof.L2TensorPower.embPow_succ_tmul
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

theorem BookProof.L2TensorPower.embPow_succ_tmul (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) :
    embPow μ (n + 1) (a ⊗ₜ[ℂ] t) = splitIso μ n (prodMk a (embPow μ n t)) := by sorry
