-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_ld_dil_one
-- name    : CompanionTheory.ThKR.LL.ld_dil_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:29.594354+00:00
-- url     : https://prove2.me/theorems/e29c3aeb-2924-45b7-95b8-e7a5b1f67090
-- title:
--   LL: ld dil one
-- statement:
--   The LL construction uses the ld dil one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/NormExpSubLe.lean#L70-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/NormExpSubLe.lean#L70-L108

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

theorem CompanionTheory.ThKR.LL.ld_dil_one {H : ℝ → Eu l →L[ℝ] Eu l} {H' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : Sch l) {F : ℝ → Sch l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vf H' f)) t₀ := by sorry
