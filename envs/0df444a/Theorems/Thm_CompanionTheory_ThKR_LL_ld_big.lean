-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_ld_big
-- name    : CompanionTheory.ThKR.LL.ld_big
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:56.573833+00:00
-- url     : https://prove2.me/theorems/97f8c96c-e5f1-41d4-bd24-655280e8c416
-- title:
--   LL: ld big
-- statement:
--   The LL construction uses the ld big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/NormExpSubLe.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/NormExpSubLe.lean#L116-L129

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem CompanionTheory.ThKR.LL.ld_big {Ai B C : ℝ → Eu l →L[ℝ] Eu l} {Ai' B' C' : Eu l →L[ℝ] Eu l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, LD (fun t => big (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = mq C' f + vf Ai' f + fou l (mq (-B') (fouInv l f)) + (c' : ℂ) • f) := by sorry
