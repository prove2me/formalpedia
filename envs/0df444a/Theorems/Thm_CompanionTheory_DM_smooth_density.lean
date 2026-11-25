-- Prove2me | Theorems.Thm_CompanionTheory_DM_smooth_density
-- name    : CompanionTheory.DM.smooth_density
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:13.224706+00:00
-- url     : https://prove2.me/theorems/655ce45d-dab2-49da-a7ea-881272d1bbad
-- title:
--   DM: smooth density
-- statement:
--   The DM construction uses the smooth density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L112-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L112-L186

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

theorem CompanionTheory.DM.smooth_density [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ δ ≤ ε, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 δ →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ h.prodExp (⇑b) '' closedBall 0 δ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by sorry
