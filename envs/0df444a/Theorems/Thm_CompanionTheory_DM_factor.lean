-- Prove2me | Theorems.Thm_CompanionTheory_DM_factor
-- name    : CompanionTheory.DM.factor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:14:56.408459+00:00
-- url     : https://prove2.me/theorems/549437ee-f1c9-4958-a223-81c49d5e1764
-- title:
--   DM: factor
-- statement:
--   The DM construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L189-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L189-L230

import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_CompanionTheory_AutomorphicTheory_PadicUnitaryWeights_DixmierMalliavin_DecompDirection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.DM
open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Metric
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
include h

theorem CompanionTheory.DM.factor [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {V : Set G} (hV : V ∈ 𝓝 1) (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ tsupport (φ i) ⊆ V ∧ tsupport (ψ i) ⊆ tsupport f) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by sorry
