-- Prove2me | Theorems.Thm_CompanionTheory_DM_decomp_iter
-- name    : CompanionTheory.DM.decomp_iter
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:12:51.708936+00:00
-- url     : https://prove2.me/theorems/135c3d45-3a13-428e-a383-c6d285c6e2cd
-- title:
--   DM: decomp iter
-- statement:
--   The DM construction uses the decomp iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L68-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean#L68-L110

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

theorem CompanionTheory.DM.decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        tsupport (F i) ⊆ tsupport f) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x)
  := by sorry
