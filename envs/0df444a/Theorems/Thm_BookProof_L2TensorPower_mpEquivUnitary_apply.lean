-- Prove2me | Theorems.Thm_BookProof_L2TensorPower_mpEquivUnitary_apply
-- name    : BookProof.L2TensorPower.mpEquivUnitary_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:29:20.934681+00:00
-- url     : https://prove2.me/theorems/ed2224e1-4b90-4130-b202-9b7c2bd21042
-- title:
--   `BookProof.L2TensorPower.mpEquivUnitary_apply` {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α} {μb : Measure β} (f : α → β) (g : β → α) (hf : MeasurePreservi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterL2TensorPowerUnitary`.
--
--   `BookProof.L2TensorPower.mpEquivUnitary_apply` {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α} {μb : Measure β} (f : α → β) (g : β → α) (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μb μa) (hgf : ∀ x, g (f x) = x) (h : Lp ℂ 2 μb) : (mpEquivUnitary f g hf hg hgf h : α → ℂ) =ᵐ[μa] fun x => (h : β → ℂ) (f x)
--
--   Formalization note: Lean 4 identifier `BookProof.L2TensorPower.mpEquivUnitary_apply`.

-- Generated from ChapterL2TensorPowerUnitary.lean — theorem BookProof.L2TensorPower.mpEquivUnitary_apply
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

theorem BookProof.L2TensorPower.mpEquivUnitary_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} (f : α → β) (g : β → α) (hf : MeasurePreserving f μa μb)
    (hg : MeasurePreserving g μb μa) (hgf : ∀ x, g (f x) = x) (h : Lp ℂ 2 μb) :
    (mpEquivUnitary f g hf hg hgf h : α → ℂ) =ᵐ[μa] fun x => (h : β → ℂ) (f x) := by sorry
