-- Prove2me | Theorems.Thm_BookProof_L2TensorPower_embPow_succ_tmul_ae
-- name    : BookProof.L2TensorPower.embPow_succ_tmul_ae
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:28:28.987517+00:00
-- url     : https://prove2.me/theorems/34c4ff5a-868a-4be9-b45d-03e76ecfddac
-- title:
--   `BookProof.L2TensorPower.embPow_succ_tmul_ae` (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) : (embPow μ (n + 1) (a ⊗ₜ[ℂ] t) : (Fin (n + 1) → V) → ℂ) =ᵐ[piMeasure...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterL2TensorPowerUnitary`.
--
--   `BookProof.L2TensorPower.embPow_succ_tmul_ae` (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) : (embPow μ (n + 1) (a ⊗ₜ[ℂ] t) : (Fin (n + 1) → V) → ℂ) =ᵐ[piMeasure μ (n + 1)] fun x => (a : V → ℂ) (x 0) * (embPow μ n t : (Fin n → V) → ℂ) (Fin.tail x)
--
--   Formalization note: Lean 4 identifier `BookProof.L2TensorPower.embPow_succ_tmul_ae`.

-- Generated from ChapterL2TensorPowerUnitary.lean — theorem BookProof.L2TensorPower.embPow_succ_tmul_ae
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

theorem BookProof.L2TensorPower.embPow_succ_tmul_ae (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) :
    (embPow μ (n + 1) (a ⊗ₜ[ℂ] t) : (Fin (n + 1) → V) → ℂ) =ᵐ[piMeasure μ (n + 1)]
      fun x => (a : V → ℂ) (x 0) * (embPow μ n t : (Fin n → V) → ℂ) (Fin.tail x) := by sorry
